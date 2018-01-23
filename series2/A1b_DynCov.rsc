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

str original = "Empire";

loc updateAuthority (loc l) {
	l.authority = original;
	return l;
}

/* Returns a tuple of statements to instrument: (insert, method, statement). */
list[tuple[loc i, loc m, loc s]] instrumentClassMethod (loc methodLocation, Statement methodBody) {
	list[tuple[loc c, loc m, loc s]] logs = [];
	
	visit (methodBody) {
		case s_ifElse : \if(_, Statement thenBranch, Statement elseBranch) :
			logs = logs + [<inBlock(thenBranch.src), methodLocation, updateAuthority(thenBranch.src)>,
						   <inBlock(elseBranch.src), methodLocation, updateAuthority(elseBranch.src)>];
		case s_case : \case(_) :
			logs = logs + <s_case.src, methodLocation, updateAuthority(s_case.src)>;
			
		case s_dcase: \defaultCase() :
			logs = logs + <s_dcase.src, methodLocation, updateAuthority(s_dcase.src)>;

		case s_do: \do(Statement body,_) :
			logs = logs + <inBlock(body.src), methodLocation, updateAuthority(s_do.src)>;
			
		case s_forEach: \foreach(_, _, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, updateAuthority(s_forEach.src)>;
			
		case s_forCond: \for(_, _, _, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, updateAuthority(s_forCond.src)>;
			
		case s_for: \for(_, _, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, updateAuthority(s_for.src)>;
			
		case s_if: \if(_, Statement thenBranch) :
			logs = logs + <inBlock(thenBranch.src), methodLocation, updateAuthority(s_if.src)>;
			
		case s_label: \label(_, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, updateAuthority(s_label.src)>;
			
		case s_while: \while(_, Statement body) :
			logs = logs + <inBlock(body.src), methodLocation, updateAuthority(s_while.src)>;			
	}
	
	return logs;
}

rel[str f, str m, str s] instrumentClass (loc file) {
	
	// 1. Create the AST.
	Declaration ast = createAstFromFile(file, true);
	list[tuple[loc i, loc m, loc s]] items = [];
	loc empty = |cwd:///|;
	
	// 2. Create all logs.
	visit (ast) {
		case m: \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions, Statement impl) :
			items = items + <inBlock(impl.src), updateAuthority(m.src), empty> + instrumentClassMethod(updateAuthority(m.src), impl); 	
	}
	
	// 3. Sort logs in decreasing order.
	items = sort(items, bool(<loc a, loc _, loc _>, <loc b, loc _, loc _>) { return a.offset > b.offset; });
	
	
	// 4. Instrument the given file with the logs.
	for (<location, method, statement> <- items) {
		appendToFile(location, "DynamicLogger.getInstance().hit(\"", updateAuthority(file), "\",\"", method, "\",\"", statement,"\");");
	}

	
	// 5. Return a list of logs to compare the instrumented results to. 
	return {<"<updateAuthority(f)>","<m>","<s>"> | <f,m,s> <- items};
}

/* Instruments a complete project. Returns a set of all logs to be expected in the logFile. */
rel[str f, str m, str s] instrumentProject (loc projectPath) {

	// 1. Create project.
	fs = crawl(projectPath);
	
	// 2. Collect all logs for non-test files.
	rel[str f, str m, str s] totalLogs = ({} | it + instrumentClass(f) | /file(loc f) := fs, !startsWith(f.file, "."), f.extension == "java", !contains(f.path, "/test"));
	
	return totalLogs;
}

/* Performs analysis of the retrieved logFile. Requires you provide it with the total set of expected logs */
void analyzeLogFile (loc logFile, rel[str f, str m, str s] allLogs) {
	str logStr = readFile(logFile);
	str empty = "|cwd:///|";
	
	// 1. Split the file into logs (one per line).
	list[str] logs = split("\n", logStr);
	rel[str f, str m, str s] relLogs = {};
	
	// 2. For each log, split it on the & symbol. Then parse all three components.
	for (log <- logs) {
		list[str] components = split("&", log);
		relLogs = relLogs + <components[0], components[1], components[2]>;
	}
	
	// 3. Extract all Methods and all Statements from the given logs.
	rel[str f, str m, str s] allMethods = {<f,m,s> | <f,m,s> <- allLogs, s == empty};
	rel[str f, str m, str s] allStatements = allLogs - allMethods;
	
	// 4. Extract all hit Methods and hit Statements from the imported logs.
	rel[str f, str m, str s] hitMethods = {<f,m,s> | <f,m,s> <- relLogs, s == empty};
	rel[str f, str m, str s] hitStatements = relLogs - hitMethods;
	
	// 6. Construct method relations: Total Statements v. Hit Statements.
	rel[str m, int t, int h] methodStatementRelations = {};
	for (<_,m,_> <- allMethods ) {
		int ts = size({ s | <_,m,s> <- allStatements });
		int hs = size({ s | <_,m,s> <- hitStatements });
		methodStatementRelations = methodStatementRelations + <m, ts, hs>;
	}
	
	// 8. Construct file relations: Methods Defined v. Methods Called.
	rel[str f, int d, int h] fileMethodRelations = {};
	for (<f,_,_> <- allMethods) {
		int ts = size({ m | <f,m,_> <- allMethods });
		int hs = size({ m | <f,m,_> <- hitMethods });
		fileMethodRelations = fileMethodRelations + <f, ts, hs>;
	}
	
	// 9. Construct file statement relations: Total Statements v. Hit Statements.
	rel [str f, int t, int h] fileStatementRelations = {};
	for (<f,_,_> <- fileMethodRelations) {
		int ts = size({ s | <f,_,s> <- allStatements });
		int hs = size({ s | <f,_,s> <- hitStatements });
		fileStatementRelations = fileStatementRelations + <f, ts, hs>;
	}
	
	println("***************************** A1 b_DynCov: RESULTS *********************************"); 
	println("FACTS:");
	println("\tProject features <size(allMethods)> total methods and <size(allStatements)> total statements.");
	println("\tCoverage: (<size(hitMethods)>/<size(allMethods)>) methods covered. (<size(hitStatements)>/<size(allStatements)>) statements covered overall");
	println("\tTotal Methods\t\tCovered Methods\t\tFile");
}

/* Runs the dynamic analysis program */
rel[str f, str m, str s] doInstrumentation () {
	loc projectFile = |project://Empire|;
	
	return instrumentProject (projectFile);
}

void doAnalysis (rel[str f, str m, str s] allLogs){
	loc logFile = |project://Empire/src/dynlogs.csv|;
	analyzeLogFile(logFile, allLogs);
}

