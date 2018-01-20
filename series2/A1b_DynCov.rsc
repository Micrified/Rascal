module sqat::series2::A1b_DynCov

import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;
import util::FileSystem;
import String;
import Set;
import Java17ish;

/*

Assignment: instrument (non-test) code to collect dynamic coverage data.

- Write a little Java class that contains an API for collecting coverage information
  and writing it to a file. NB: if you write out CSV, it will be easy to read into Rascal
  for further processing and analysis (see here: lang::csv::IO)

- Write two transformations:
  1. to obtain method coverage statistics
     (at the beginning of each method M in class C, insert statement `hit("C", "M")`
  2. to obtain line-coverage statistics
     (insert hit("C", "M", "<line>"); after every statement.)

The idea is that running the test-suite on the transformed program will produce dynamic
coverage information through the insert calls to your little API.

Questions
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)
- which methods have full line coverage?
- which methods are not covered at all, and why does it matter (if so)?
- what are the drawbacks of source-based instrumentation?

Tips:
- create a shadow JPacman project (e.g. jpacman-instrumented) to write out the transformed source files.
  Then run the tests there. You can update source locations l = |project://jpacman/....| to point to the 
  same location in a different project by updating its authority: l.authority = "jpacman-instrumented"; 

- to insert statements in a list, you have to match the list itself in its context, e.g. in visit:
     case (Block)`{<BlockStm* stms>}` => (Block)`{<BlockStm insertedStm> <BlockStm* stms>}` 
  
- or (easier) use the helper function provide below to insert stuff after every
  statement in a statement list.

- to parse ordinary values (int/str etc.) into Java15 syntax trees, use the notation
   [NT]"...", where NT represents the desired non-terminal (e.g. Expr, IntLiteral etc.).  

*/

/* Returns methods that are not constructors */
set[loc] nonConstructorMethods (rel[loc, loc] methods) {
	return {m | <_,m> <- methods, !isConstructor(m) };
}


loc afterBrace (loc l) {
	println("Original location: <l>");
	l.offset = l.offset + 1;
	l.length = 0;
	println("New location: <l>");
	return l;
}

void instrumentClass (loc file) {
	
	// 1. Create the AST.
	Declaration ast = createAstFromFile(file, true);
	list[tuple[loc l, str methodName]] items = [];
	
	// 2. Instrument all methods.
	visit (ast) {
		case m: \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions, Statement impl) :
			items = items + <afterBrace(impl.src), name>;
	}
	
	// 3. Sort list.
	items = sort(items, bool(<loc a, str _>, <loc b, str _>) { return a.offset > b.offset; });
	
	for (<location, methodName> <- items) {
		appendToFile(location, "DynamicLogger.getInstance.hit(", file.file, ",", methodName, ");");
	}
}

set[loc] instrumentProject (loc projectPath) {

	// 1) Create project.
	M3 project = createM3FromEclipseProject(projectPath);
	
	// 2. Extract all methods: Excluding Constructors.
	set[loc] allMethods = nonConstructorMethods(declaredMethods(project));
	
	set[Declaration] decls = createAstsFromEclipseProject(project, true); 
	
	//3. 
	return allMethods;
}


void methodCoverage(loc project) {
  // to be done
}

void lineCoverage(loc project) {
  // to be done
}



// Helper function to deal with concrete statement lists
// second arg should be a closure taking a location (of the element)
// and producing the BlockStm to-be-inserted 
BlockStm* putAfterEvery(BlockStm* stms, BlockStm(loc) f) {
  
  Block put(b:(Block)`{}`) = (Block)`{<BlockStm s>}`
    when BlockStm s := f(b@\loc);
  
  Block put((Block)`{<BlockStm s0>}`) = (Block)`{<BlockStm s0> <BlockStm s>}`
    when BlockStm s := f(s0@\loc);
  
  Block put((Block)`{<BlockStm s0> <BlockStm+ stms>}`) 
    = (Block)`{<BlockStm s0> <BlockStm s> <BlockStm* stms2>}`
    when
      BlockStm s := f(s0@\loc), 
      (Block)`{<BlockStm* stms2>}` := put((Block)`{<BlockStm+ stms>}`);

  if ((Block)`{<BlockStm* stms2>}` := put((Block)`{<BlockStm* stms>}`)) {
    return stms2;
  }
}


