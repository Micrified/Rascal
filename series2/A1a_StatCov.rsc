module sqat::series2::A1a_StatCov

import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;
import Node;
import util::FileSystem;
import String;
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

M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework|);

// New stuff

// Returns true if given loc is in a set of relations.
bool inRelations (loc l, Relation rs) {
	int count = ( 0 | it + 1 | /<_,_,l> <- rs);
	return count > 0;
}

Relation transitiveClosure (loc method , Relation graph) {
	return {};
} 

Relation graphProject (M3 project) {

	// Collect all class-to-method relations.
	Relation ctm = { <class, "DM", method> | class <- classes(project), method <- methods(project, class) };
	
	// Collect all method-to-method invocations.
	Relation mtm = { <source, "C", target> | <source, target> <- project.methodInvocation, inRelations(target, ctm) };
	
	// Filter all test-methods from our method-to-method invocations.
	set[loc] tst = { method | <loc method, loc annotation> <- project.annotations, contains(annotation.path, "junit") };
	
	// Obtain transitive closure of test-methods over all methods.
	Relation clo = ({} | it + r | r <- [ transitiveClosure(method, mtm) | method <- tst ]);
	
	// Return all relations
	return ctm + mtm;
}


// Old stuff

Relation getFileToMethodRelations (loc f) {
	Relation rs = {};
 	if (startsWith(f.file, ".") || f.extension != "java") {
 		return rs;
 	}
 	
 	Declaration fileAST = createAstFromFile(f, true);
 	
 	visit (fileAST) {
 		case m1 : \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions, Statement impl) :
 			rs = rs + <f, "dm", m1.src>;
 		case m2 : \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions) :
 			rs = rs + <f, "dm", m2.src>;
 	}
 	return rs;
}

Relation makeProjectGraph (loc project) {
	Relation rs = {};
	fs = crawl(project);
	
	visit (fs) {
			
		case d : \directory(loc p, set[FileSystem] kids) :
			rs = rs + {<p, "dt", q> | \file(loc q) <- kids, !startsWith(q.file, "."), q.extension == "java"} + 
				{<p, "dt", r> | \directory(loc r, _) <- kids};
				
		case f : \file(loc l) :
			rs = rs + getFileToMethodRelations(l);
	}
	
	return rs;
}


