module sqat::series2::A1b_DynCov

import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import lang::csv::IO;
import IO;
import List;
import ParseTree;
import util::FileSystem;
import String;
import Set;
import Java17ish;
import util::Math;

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

/*****************************************************************************/
/*					         Global Variables						       */
/*****************************************************************************/

// Name of singleton to be imported in all files.
str importString = "nl.tudelft.DynamicLogger";

// The set of fully covered methods (line coverage).
set[loc] fullyCoveredMethods = {};

// The set of non-covered methods (line coverage).
set[loc] nonCoveredMethods = {};

/*****************************************************************************/
/*					     Instrumentation Functions						   */
/*****************************************************************************/

// Modified function: Inserts an instrumented statement before every block.
BlockStm* putBeforeEvery(BlockStm* stms, BlockStm(loc) f) {
  
  Block put(b:(Block)`{}`) = (Block)`{<BlockStm s>}`
    when BlockStm s := f(b@\loc);
  		
  Block put((Block)`{<BlockStm s0>}`) = (Block)`{<BlockStm s> <BlockStm s0>}`
    when BlockStm s := f(s0@\loc);
  
  Block put((Block)`{<BlockStm s0> <BlockStm+ stms>}`) 
    = (Block)`{<BlockStm s> <BlockStm s0> <BlockStm* stms2>}`
    when
      BlockStm s := f(s0@\loc), 
      (Block)`{<BlockStm* stms2>}` := put((Block)`{<BlockStm+ stms>}`);

  if ((Block)`{<BlockStm* stms2>}` := put((Block)`{<BlockStm* stms>}`)) {
    return stms2;
  }
}

// Inserts a custom import statement into the given CompilationUnit.
start[CompilationUnit] insertImport ((start[CompilationUnit])`<PackageDec? pkgs> <ImportDec* imps> <TypeDec* types>`) {
	ImportDec logger = parse(#ImportDec, "import <importString>;"); 
	return (start[CompilationUnit])`<PackageDec? pkgs> <ImportDec * imps> <ImportDec logger> <TypeDec* types>`;
}

// Instruments a class file.
start[CompilationUnit] instrumentClass (loc classLoc) {
	
	// Construct the parse tree for the class.
	start[CompilationUnit] parseTree = parseJava(classLoc);
	
	// Construct an instrumented method call.
	BlockStm instrumentMethod (loc methodLoc) {
		return parse(#BlockStm, "DynamicLogger.getInstance().hit(\"<classLoc>\", \"<methodLoc>\");");
	}
	
	// Constuct an instrumented statement call.
	BlockStm instrumentLine (loc methodLoc, loc lineLoc) {
		return parse(#BlockStm, "DynamicLogger.getInstance().hit(\"<classLoc>\", \"<methodLoc>\", \"<lineLoc>\");");
	}
	
	// Perform subtree replacement.
	parseTree = visit (parseTree) {
		case (MethodDec)`<MethodDecHead h> {<BlockStm* b>}` => (MethodDec)`<MethodDecHead h> {<BlockStm h2> <BlockStm* b2>}`
		  when 
		  	BlockStm* b2 := putBeforeEvery(b, BlockStm (loc lineLoc) { return instrumentLine (h@\loc, lineLoc); }),
		  	BlockStm h2 := instrumentMethod(h@\loc)
	}
	
	// Insert an import statement so the instrumented lines may use our logger.
	return insertImport(parseTree);
}

// Instrument a Java project. Automatically omits any files within a test directory marked with /test.
void instrumentProject (loc project, str shadow) {
	for(f <- files(project), f.extension == "java", !contains(f.path, "/test")) {
		start[CompilationUnit] newclass = instrumentClass(f);
		f.authority = shadow;
		writeFile(f, newclass);
	}
}

/*****************************************************************************/
/*					     Coverage Computation Functions					   */
/*****************************************************************************/

// Returns all methods in a class.
set[loc] getClassMethods (loc classLoc) {
	set[loc] ms = {};
	
	// Construct the parse tree for the class.
	start[CompilationUnit] parseTree = parseJava(classLoc);
	
	// Visit all Methods.
	visit (parseTree) {
		case (MethodDec)`<MethodDecHead h> {<BlockStm* _>}` :
			ms += h@\loc;
	}
	
	return ms;
}

// Returns relation file-to-method for a given class file.
rel[loc f, loc m] methodsPerClass (loc classLoc) {
	rel [loc f, loc m] mpc = {};
	
	// Construct the parse tree for the class.
	start[CompilationUnit] parseTree = parseJava(classLoc);
	
	// Visit all Methods.
	visit (parseTree) {
		case (MethodDec)`<MethodDecHead h> {<BlockStm* _>}` :
			mpc += <classLoc, h@\loc>;
	}
	
	return mpc;
}

// Returns relation (file (with) method (has) line) for a given class file.
rel[loc f, loc m, loc l] linesPerMethodInClass (loc classLoc) {
	rel[loc f, loc m, loc l] lpm = {};
	
	// Construct the parse tree for the class.
	start[CompilationUnit] parseTree = parseJava(classLoc);
	
	// Visit all Methods.
	visit (parseTree) {
		case (MethodDec)`<MethodDecHead h> {<BlockStm* b>}` :
			lpm += {<classLoc, h@\loc, s@\loc> | s <- b};
	}
	
	return lpm;
}

// Returns True if a given class is in the specified directory.
bool isInDirectory(loc cls, str directory) {
	return contains(resolveLocation(cls).path, directory);
}

/*****************************************************************************/
/*					     Statistical/IO Functions						   */
/*****************************************************************************/

void dynMethodCoverage(loc project, loc csv) {

	// Initialize local variables: (project classes).
	set[loc] classes = {f | f <- files(project), f.extension == "java", !contains(f.path, "/test") };

	// Returns a relationship map of each class to it's respective methods.
	rel[loc f, loc m] getTotalMethods () {
		rel[loc f, loc m] rs = {};
		for (f <- classes) {
			rs += methodsPerClass(f);
		}
		return rs;
	}

	// 1. Read logs from CSV.
	rel[loc f, loc m] hitMethods = readCSV(#rel[loc f, loc m], csv, separator = "&");
	
	// 2. Obtain actual class-to-method relations.
	rel[loc f, loc m] totalMethods = getTotalMethods();
	
	// 3. For each class, output coverage statistics.
	println("RATIO (METHODS COVERED)\t\tCLASS");
	println("--------------------------------------------------------------------------------");
	for (f <- classes) {
		int total = size({ m | <f, loc m> <- totalMethods });
		int hit = size({ m | <f, loc m> <- hitMethods });
		println("<hit>/<total>\t\t<f>");
	}
	println("--------------------------------------------------------------------------------\n");
	println("Overall Ratio (Covered methods / Total methods): <size(hitMethods)>/<size(totalMethods)>");
}

void dynLineCoverage(loc project, loc csv) {

	// Initialize local variables: (project classes).
	set[loc] classes = { f | f <- files(project), f.extension == "java", !contains(f.path, "/test") };
	
	// Returns a relationship map of line to method and class.
	rel[loc f, loc m, loc l] getTotalLines () {
		rel[loc f, loc m, loc l] rs = {};
		for (f <- classes) { 
			rs += linesPerMethodInClass(f);
		}
		return rs;
	}
	
	// 1. Read logs from CSV.
	rel[loc f, loc m, loc l] hitLines = readCSV(#rel[loc f, loc m, loc l], csv, separator = "&");
	
	// 2. Obtain actual lines-to-method-to-class relations.
	rel[loc f, loc m, loc l] totalLines = getTotalLines();
	
	// 3. For each class, for each method, output coverage statistics.
	println("CLASS\t\tRATIO (LINES COVERED)\t\tMETHOD");
	println("--------------------------------------------------------------------------------");
	for (f <- classes) {
		println("<f.file>");
		for (m <- getClassMethods(f)) {
			int total = size({ l | <f, m, loc l> <- totalLines });
			int hit = size({ l | <f, m, loc l> <- hitLines });
			println("\t\t\t\t<hit>/<total>\t\t<m>");
			
			if (total == hit && total > 0) {
				fullyCoveredMethods += m;
			}
			if (total == 0) {
				nonCoveredMethods += m;
			}
		}
	}
	println("--------------------------------------------------------------------------------\n");
	println("Overall Ratio (Covered lines / Total lines): <size(hitLines)>/<size(totalLines)>");
}

void a1b (loc project) {

	// 1. Show Method Coverage.
	dynMethodCoverage(project, |project://jpacman-instrumented/dynMethodLogs.csv|);
	
	// 2. Show Line Coverage.
	dynLineCoverage(project, |project://jpacman-instrumented/dynLineLogs.csv|);
	
	// 3. Answer Questions.
	println("Which methods have full line coverage?");
	println("--------------------------------------------------------------------------------");
	for (m <- fullyCoveredMethods) {
		println("<m>");
	}
	println("--------------------------------------------------------------------------------\n");
	
	println("Which methods are not covered at all?");
	for (m <- nonCoveredMethods) {
		println("<m>");
	}
	println("--------------------------------------------------------------------------------\n");
	
	println("What are the drawbacks of source-based instrumentation?");
	println("--------------------------------------------------------------------------------");
	println("1. You need a working installation of the project.");
	println("2. An assessor may not have access to required software or hardware.");
	println("3. The build or deployment process may not be reproducible.");
	println("4. The software might require proprietary libraries under a non-transferrable license.");
	println("5. Instrumentation might not be feasible for software running on embedded devices.");
	println(" ( via. \"Static Estimation of Test Coverage\" by Tiago L. Alves & Joost Visser)");
	
}




