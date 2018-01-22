module sqat::series1::A1_SLOC

import IO;
import ParseTree;
import Boolean;
import String;
import util::FileSystem;
import Map;
import util::Math;

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

/* Given a file as a string, the purify function removes the following
 * using Regular Expressions.
 * 1. String literals. Replaced by empty string.
 * 2. Block comments: Replaced by empty string.
 * 3. Line comments: Replaced by empty string.
 * 4. Newline + whitespace: Replaced by a single newline.
*/
str purify (str source) {

	// 1) Filter out string literals.
	set[str] stringLiterals = { match | /<match: \"([^\"])*\" >/ := source };
	source = (source | replaceAll(it, comment, "\"\"") | comment <- stringLiterals);
	
	// 2) Filter out block comments.
	set[str] blockComments = { match | /<match: \/\*(\*[^\/]|[^\*])*\*\/>/ := source };
	source = (source | replaceAll(it, comment, "") | comment <- blockComments);
	
	// 3) Filter out line comments.
	set[str] lineComments = { match | /<match: \/\/(.)*>/ := source };
	source = (source | replaceAll(it, comment, "") | comment <- lineComments);

	// 4) Filter out consecutive whitespace.
	set[str] whitespaceSequences = { match | /<match:[\t\ ]+>/ := source };
	source = (source | replaceAll(it, sequence, "") | sequence <- whitespaceSequences);
	 
	return source;
}

/* Returns the number of source lines for a given file. */
int sourceLines (loc file) {
	str purifiedFile = purify(readFile(file));
	list[str] segmentedFile = split("\n", purifiedFile);
	return size([line | line <- segmentedFile, line != ""]);
}

/* Returns mapping: Files to Lines-Of-Code */
SLOC sloc (loc project) {
	fs = crawl(project);
	SLOC result = (l : sourceLines(l) | /file(loc l) := fs, !startsWith(l.file, "."), l.extension == "java");
	return result;
}

/* Main Program */
void main () {
	SLOC slocMap = sloc(|project://jpacman-framework|);

	// What is the biggest file in JPacman?
	println("************************** A1_SLOC: RESULTS ******************************");
	loc f = (getOneFrom(slocMap) | slocMap[it] > slocMap[s] ? it : s | s <- slocMap);
	println("Largest File: < f.path >. Featuring: < slocMap[f] > source lines of code.");

	// What is the total size of JPacman?
	int t = (0 | it + slocMap[s] | s <- slocMap);
	println("Total Size: < t > source lines of code, over < size(slocMap) > files.");

	// Is JPacman large according to SIG maintainability?
	println("SIG Maintainability model assigns JPmacan a \"++\" rating as it is a Java project with 0-66k LOC, meaning the project is extremely small.");
	
	// What is the ratio between actual code and test code size?
	SLOC actualLOC = sloc(|project://jpacman-framework/src/main|);
	SLOC testLOC	= sloc(|project://jpacman-framework/src/test|);
	int actualLOCSize = (0 | it + actualLOC[s] | s <- actualLOC);
	int testLOCSize = (0 | it + testLOC[s] | s <- testLOC);
	real ratio = toReal(actualLOCSize) / toReal(testLOCSize);
	println("There are <actualLOCSize> actual lines of code vs <testLOCSize> test lines of code. Giving ratio: <ratio>");
}
   
             