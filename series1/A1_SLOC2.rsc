module sqat::series1::A1_SLOC

import IO;
import ParseTree;
import String;
import util::FileSystem;

/* 

Count Source Lines of Code (SLOC) per file:
- ignore comments
- ignore empty lines

Tips
- use locations with the project scheme: e.g. |project:///jpacman/...|
- functions to crawl directories can be found in util::FileSystem
- use the functions in IO to read source files

Answer the following questions:
- what is the biggest file in JPacman?
- what is the total size of JPacman?
- is JPacman large according to SIG maintainability?
- what is the ratio between actual code and test code size?

Sanity checks:
- write tests to ensure you are correctly skipping multi-line comments
- and to ensure that consecutive newlines are counted as one.
- compare you results to external tools sloc and/or cloc.pl

Bonus:
- write a hierarchical tree map visualization using vis::Figure and 
  vis::Render quickly see where the large files are. 
  (https://en.wikipedia.org/wiki/Treemapping) 

*/

alias SLOC = map[loc file, int sloc];

// |project://jpacman-framework/src|

int sourceLines (loc file) {
	allLines = readFileLines(file);
	tokens = tokenize(file);
	
	for t in tokens {
		if match("\\(.)*\n") {
			continue;
		}
		if match("(no
	}
	
	
	return size(allLines);
}

SLOC sloc(loc project) {
  SLOC result = ();
  fs = crawl(project);
  result = (l : sourceLines(l)  | /file(loc l) := fs, !startsWith(l.file, "."), l.extension == "java");
  return result;
}


// Example Exercise: Finding all big methods in some classes.   
// rascal>parse(#start[CompilationUnit], |project://jpacman-framework/src/main/java/nl/tudelft/jpacman/game/Game.java|);
// visit (pt) { case (MethodDec)` <MethodDecHead m> <MethodBody b_>`: println(m); }
module Message

data Message = error (str msg, loc at) | warning(...) | info(...)

set[Message] checkStyle (loc project) {
	set[Message] result = {};

} 

// "start" in this case means begin with layout and end with layout. Ignore stuff prior to import lines and stuff(?).
// The @\loc is "an annotation of the parse tree". Kind of analogus to theMethod.loc.
map[loc, int] methodSLOC(start[ComplicationUnit] cu) {
	visit (cu) {
		case theMethod:(MethodDec)`<MethodDecHead m> <MethodBody _>`:
			println(m);
			result[theMethod@\loc] = sloc("<body>");
			
		// Write a case for constructors (if you want to count them).
		// Write the entire thing as a single comprehension.
		// You would want to do it with deep match. Whatever that means.
	}
	return result;
}  

// Function designed to filter methods against some threshhold. 
// Says: Only keep entries in the map for which the SLOC numbers are > than the threshold.
map[loc, int] bigMethods(int threshold, map[loc, int]methodSLOC) {
	return (l: | loc l <- methodSLOC, methodSLOC[l] >= threhold);
}

// You may use resource markers to hide large file path links that Rascal tends to output.
// The message stuf is in util::ResourceMarkers.
set[Message] warningsForBigMethods(map[loc, int] ms) = 
	{ warning("Big method!", l) | l <- ms };

   
             