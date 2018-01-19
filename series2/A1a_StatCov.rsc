module sqat::series2::A1a_StatCov

import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;
import Node;
import util::FileSystem;
import String;
import Set;

/*

Implement static code coverage metrics by Alves & Visser 
(https://www.sig.eu/en/about-sig/publications/static-estimation-test-coverage)


The relevant base data types provided by M3 can be found here:

- module analysis::m3::Core:

rel[loc name, loc src]        M3.declarations;            // maps declarations to where they are declared. contains any kind of data or type or code declaration (classes, fields, methods, variables, etc. etc.)
rel[loc name, TypeSymbol typ] M3.types;                   // assigns types to declared source code artifacts
rel[loc src, loc name]        M3.uses;                    // maps source locations of usages to the respective declarations
rel[loc from, loc to]         M3.containment;             // what is logically contained in what else (not necessarily physically, but usually also)
list[Message]                 M3.messages;                // error messages and warnings produced while constructing a single m3 model
rel[str simpleName, loc qualifiedName]  M3.names;         // convenience mapping from logical names to end-user readable (GUI) names, and vice versa
rel[loc definition, loc comments]       M3.documentation; // comments and javadoc attached to declared things
rel[loc definition, Modifier modifier] M3.modifiers;     // modifiers associated with declared things

- module  lang::java::m3::Core:

rel[loc from, loc to] M3.extends;            // classes extending classes and interfaces extending interfaces
rel[loc from, loc to] M3.implements;         // classes implementing interfaces
rel[loc from, loc to] M3.methodInvocation;   // methods calling each other (including constructors)
rel[loc from, loc to] M3.fieldAccess;        // code using data (like fields)
rel[loc from, loc to] M3.typeDependency;     // using a type literal in some code (types of variables, annotations)
rel[loc from, loc to] M3.methodOverrides;    // which method override which other methods
rel[loc declaration, loc annotation] M3.annotations;

Tips
- encode (labeled) graphs as ternary relations: rel[Node,Label,Node]
- define a data type for node types and edge types (labels) 
- use the solve statement to implement your own (custom) transitive closure for reachability.

Questions:
- what methods are not covered at all?
- how do your results compare to the jpacman results in the paper? Has jpacman improved?
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)

*/

alias Relation = rel[loc from, str cType, loc to];

alias Coverage = tuple[loc l, int dm, int cm];

M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework|);

// New stuff

// Returns true if given loc is in a set of relations.
bool inRelations (loc l, Relation rs) {
	int count = ( 0 | it + 1 | /<_,_,l> <- rs);
	return count > 0;
}

// Returns all methods "a" calls "b" where "a" is called from the source set, and "b" is a method "a" called. 
Relation transitiveClosure (Relation testMethods , Relation graph) {
	// { <a, "C", c> | <a, "C", b> <- testMethods, <b,"C",c> <- graph };
	return { <b, "C", c> | <_, "C", b> <- testMethods, <b,"C",c> <- graph };
}

Relation testMethodCoverage (M3 project) {

	// Obtain project graph.
	Relation graph = graphProject(project);

	// Filter all test-methods from our project: Assumes all test-methods are annotated.
	Relation testMethods = { <method, "C", target> | <loc method, loc annotation> <- project.annotations, contains(annotation.path, "junit"), <method, "C", target> <- graph };

	solve (testMethods) { 
		testMethods = testMethods + transitiveClosure(testMethods, graph); 
	}
				
	return testMethods;
}

Relation graphProject (M3 project) {

	// Collect all package-to-class relations.
	Relation ptc = { <package, "DT", class> | package <- packages(project), class <- classes(project), contains(class.path, package.path) };

	// Collect all class-to-method relations.
	Relation ctm = { <class, "DM", method> | class <- classes(project), method <- methods(project, class) };
	
	// Collect all method-to-method invocations.
	Relation mtm = { <source, "C", target> | <source, target> <- project.methodInvocation, inRelations(target, ctm) };
	
	// Return all relations
	return ptc + ctm + mtm;
}

list[Coverage] computeClassCoverage (M3 project) {

	// Obtain Test Method Coverage (Relations).
	Relation testCoverage = testMethodCoverage(project);
	
	set[loc] ts = {method | <loc method, loc annotation> <- project.annotations, contains(annotation.path, "junit")};
	
	// Extract all Test Methods in Relations.
	set[loc] tms = { m | <m,_,_> <- testMethodCoverage(project) } + 
				   { m | <_,_,m> <- testMethodCoverage(project) };
	
	// Compute class coverage.
	return [<c, size(methods(project, c) - ts), size(methods(project, c) - tms)> | c <- classes(project)];
} 

// Class Coverage: <Class Location, N.Defined Methods, N.Covered Methods>
Coverage computeClassCoverage (loc cls,  set[loc] defined, set[loc] tested) {
	return <cls, size(defined), size(tested & defined)>; 
}

// Package Coverage: <Package Location, N.Defined Methods, N.Covered Methods>
Coverage computePackageCoverage (loc pkg, list[Coverage] clsCoverage) {
	list[Coverage] pkgCoverage = [<cls, dm, cm> | <cls, dm, cm> <- clsCoverage, contains(cls.path, pkg.path) ]; 
	int defined = (0 | it + n | <cls, n, _> <- pkgCoverage);
	int covered = (0 | it + n | <cls, _, n> <- pkgCoverage);
	return <pkg, defined, covered>;
}

Coverage computeStaticCoverage (loc projectPath) {

	// Create M3 project.
	M3 project = createM3FromEclipseProject(projectPath);

	// ********************* Compute Project Graph ************************** 

	// Collect all package-to-class relations.
	Relation ptc = { <pkg, "DT", cls> | pkg <- packages(project), cls <- classes(project), contains(cls.path, pkg.path) };

	// Collect all class-to-method relations.
	Relation ctm = { <cls, "DM", mth> | cls <- classes(project), mth <- methods(project, cls) };
	
	// Collect all method-to-method relations.
	Relation mtm = { <src, "C", tgt> | <src, tgt> <- project.methodInvocation, inRelations(tgt, ctm) };
	
	// ********************* Compute Test Coverage ************************** 
	
	// Filter all test-methods from our project: Assumes all test-methods are annotated.
	Relation trs = { <method, "C", target> | <loc method, loc annotation> <- project.annotations, contains(annotation.path, "junit"), <method, "C", target> <- mtm };

	// Compute transitive closure over test-methods and method-to-method relations.
	solve (trs) { 
		trs = trs + transitiveClosure(trs, mtm); 
	}
	
	// Extract all covered test methods from transitive relations.
	set[loc] covered = {t | <t,_,_> <- trs} + {t | <_,_,t> <- trs};
	
	// ********************* Compute Test Coverage **************************
	
	// Compute the class coverage.
	list[Coverage] classCoverage = [computeClassCoverage(cls, methods(project, cls), covered) | cls <- classes(project) ];
	
	// Compute the package coverage.
	list[Coverage] pkgCoverage = [computePackageCoverage(pkg, classCoverage) | pkg <- packages(project) ];
	
	// Compute the project coverage.
	Coverage projectCoverage = <projectPath, (0 | it + dm | <_,dm,_> <- pkgCoverage), (0 | it + cm | <_,_,cm> <- pkgCoverage)>;

	return projectCoverage;
}




