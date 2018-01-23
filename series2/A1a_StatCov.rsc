module sqat::series2::A1a_StatCov

import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;
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

/*******************************************************************************************/

/* Returns all test classes */
set[loc] getTestClasses (str directory, set[loc] allClasses) {
	return { cls | cls <- allClasses, contains(resolveLocation(cls).path, directory) };
}

/* Returns methods that are not constructors */
set[loc] nonConstructorMethods (rel[loc, loc] methods) {
	return {m | <_,m> <- methods, !isConstructor(m) };
}

void computeStaticCoverage (loc projectPath) {

	// 1. Initialize an M3 instance from the project.
	M3 project = createM3FromEclipseProject(projectPath);
	
	// 2. Extract all packages. 
	set[loc] allPackages = packages(project);
	
	// 3. Extract all classes.
	set[loc] allClasses = classes(project);
	
	// 4. Extract all methods: Excluding Constructors.
	set[loc] allMethods = nonConstructorMethods(declaredMethods(project));
	
	// 5. Extract all test classes.
	set[loc] testClasses = getTestClasses("test", allClasses);
	
	// 6. Extract all test methods.
	set[loc] testMethods = ( {} | it + (methods(project, c) & allMethods) | c <- testClasses);
	
	// 7. Compute all method-to-method relations.
	rel[loc a, loc b] methodRelations = { <a,b> | <a,b> <- project.methodInvocation, a in allMethods, b in allMethods };
	
	// *. Compute all dynamic-dispatch relations (If x calls y, and y is overridden by z, then x may have called z too.
	methodRelations = methodRelations + { <x,z> | <x,y> <- methodRelations, <z,y> <- project.methodOverrides }; 
	
	// 8. Compute coverage by tests.
	rel[loc a, loc b] testCoverage = { <a,b> | <a,b> <- project.methodInvocation, a in testMethods, b in allMethods };
	solve (testCoverage) {
		testCoverage = testCoverage + (testCoverage o methodRelations);
	}
	
	// 9. Compute all covered methods
	set[loc] coveredMethods = { m | <m,_> <- testCoverage} + { m | <_,m> <- testCoverage} - testMethods;
	
	// 10. Compute all non-covered methods
	set[loc] nonCoveredMethods = (allMethods - testMethods) - coveredMethods;

	println("***************************** A1a_StatCov: RESULTS *********************************");
	println("FACTS");
	println("\tNumber of methods: <size(allMethods - testMethods)>");
	println("\tNumber of covered methods: <size(coveredMethods)>");
	
	println("QUESTIONS");
	println("\tWhat methods are not covered?");
	println("\tThere are <size(nonCoveredMethods)> total non-covered methods");
	println("\n\tCovered\t\tNot-Covered\t\tClass Name");
	println("---------------------------------------------------------------");
	for (c <- allClasses) {
		set[loc] allDeclaredClassMethods = { declaredMethod | declaredMethod <- methods(project, c), declaredMethod in allMethods };
		set[loc] coveredClassMethods = { declaredMethod | declaredMethod <- allDeclaredClassMethods, declaredMethod in coveredMethods };
		set[loc] notCoveredClassMethods = allDeclaredClassMethods - coveredClassMethods;
		println("\t<size(coveredClassMethods)>\t\t<size(notCoveredClassMethods)>\t\t<c.file>");	
	}
	println("---------------------------------------------------------------");
	
	/* How do the results compare ? 
     * Paper got 84.53% coverage. We got 61% coverage (105/172). So a decent amount less.
     * Clover reports 76.6% coverage. Closer to the paper than ours.
	
	*/
}


