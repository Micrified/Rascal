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

/* Adjusts a given location for a block such that the returned location lies just within said block */
loc inBlock (loc l) {
	l.offset = l.offset + 1;
	l.length = 0;
	return l;
}

/* Returns a tuple of statements to instrument: (insert, method, statement). */
list[tuple[loc i, loc m, loc s]] instrumentClassMethod (loc methodLocation, Statement methodBody) {
	list[tuple[loc c, loc m, loc s]] logs = [];
	
	visit (methodBody) {
		case s_ifElse : \if(Expression condition, Statement thenBranch, Statement elseBranch) :
			logs = logs + [<inBlock(thenBranch.src), methodLocation, thenBranch.src>,
						   <inBlock(elseBranch.src), methodLocation, elseBranch.src>];
		case s_case : \case(_) :
			logs = logs + <s_case.src, methodLocation, s_case.src>;
			
		case s_dcase: \defaultCase() :
			logs = logs + <s_dcase.src, methodLocation, s_dcase.src>;

		case s_do: \do(Statement body, Expression condition) :
			logs = logs + <inBlock(body.src), methodLocation, s_do.src>;
			
		case s_forEach: \foreach(Declaration parameter, Expression collection, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, s_forEach.src>;
			
		case s_forCond: \for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, s_forCond.src>;
			
		case s_for: \for(list[Expression] initializers, list[Expression] updaters, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, s_for.src>;
			
		case s_if: \if(Expression condition, Statement thenBranch) :
			logs = logs + <inBlock(thenBranch.src), methodLocation, s_if.src>;
			
		case s_label: \label(str name, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, s_label.src>;
			
		case s_while: \while(Expression condition, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, s_while.src>;			
	}
	
	return logs;
}

void instrumentClass (loc file) {
	
	// 1. Create the AST.
	Declaration ast = createAstFromFile(file, true);
	list[tuple[loc i, loc m, loc s]] items = [];
	loc empty = |cwd:///|;
	
	// 2. Instrument all methods.
	visit (ast) {
		case m: \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions, Statement impl) :
			items = items + <inBlock(impl.src), m.src, empty> + instrumentClassMethod(m.src, impl); 	
	}
	
	// 3. Sort list.
	items = sort(items, bool(<loc a, loc _, loc _>, <loc b, loc _, loc _>) { return a.offset > b.offset; });
	
	for (<location, method, statement> <- items) {
		if (statement == empty) {
			appendToFile(location, "DynamicLogger.getInstance().hit(\"", file, "\",\"", method, "\");");
		} else {
			appendToFile(location, "DynamicLogger.getInstance().hit(\"", file, "\",\"", method, "\",\"", location,"\");");
		}	
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


