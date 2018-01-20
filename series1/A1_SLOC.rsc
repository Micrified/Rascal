module sqat::series1::A1_SLOC

import IO;
import ParseTree;
import Boolean;
import String;
import util::FileSystem;
import Map;

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

str removeComments (str source) {

	// 1) Filter out string literals.
	set[str] stringLiterals = { match | /<match: \"([^\"])*\" >/ := source };
	source = (source | replaceAll(it, comment, "\"\"") | comment <- stringLiterals);
	
	// 1) Filter out block comments.
	set[str] blockComments = { match | /<match: \/\*(\*[^\/]|[^\*])*\*\/>/ := source };
	source = (source | replaceAll(it, comment, "") | comment <- blockComments);
	
	// 2) Filter out line comments.
	set[str] lineComments = { match | /<match: \/\/(.)*>/ := source };
	source = (source | replaceAll(it, comment, "") | comment <- lineComments);
	
	// 3) Filter out consecutive newlines.
	 set[str] newlineSequences = { match | /<match:\n(\s)*>/ := source };
	 source = (source | replaceAll(it, sequence, "\n") | sequence <- newlineSequences);
	 
	return source;
}

/* Filters out all character sequences detected to be comments */
str filterComments (str s) {
	list[int] ns = [], cs = chars(s);
	
	while (size(cs) > 0) {
	
		// Ignore string literals.
		if (startsWith(stringChars(cs), "\"")) {
			ns = push(head(cs), ns); cs = drop(1,cs);
			while (!startsWith(stringChars(cs), "\"")) {
				ns = push(head(cs), ns); cs = drop(1,cs);
			}
			ns = push(head(cs), ns); cs = drop(1,cs);
		}
		
		// Filter block comments.
		if (startsWith(stringChars(cs), "/*")) {
			cs = drop(2, cs);
			while (!startsWith(stringChars(cs), "*/")) {
				cs = drop(1, cs);
			}
			cs = drop(2,cs);
		}
		
		// Filter line comments.
		if (startsWith(stringChars(cs), "//")) {
			cs = drop(2, cs);
			while (!startsWith(stringChars(cs), "\n")) {
				cs = drop(1, cs);
			}
			cs = drop(1,cs);
		}
		
		if (size(cs) > 0) {
			ns = push(head(cs), ns); cs = drop(1,cs);
		}
	}
	
	// Reverse sequence, since we were pushing to it.
	return stringChars(reverse(ns));
}

/* Filters out all newline sequences from the given string */
str filterConsecutiveNewlines (str s) {
	list[int] ns = [], cs = chars(s);
	
	while (size(cs) > 0) {
	
		// Ignore all consecutive whitespace after a newline.
		if (startsWith(stringChars(cs), "\n")) {
			ns = push(head(cs), ns); cs = drop(1,cs);
			
			while (startsWith(stringChars(cs), " ") || startsWith(stringChars(cs), "\t") || startsWith(stringChars(cs), "\n")) {
				cs = drop(1,cs);
			}
		}
		if (size(cs) > 0) {
			ns = push(head(cs), ns); cs = drop(1,cs); 
		}
	}
	
	// Reverse sequence, since we were pushing to it.
	return stringChars(reverse(ns));
}

/* Returns number of source codes for file */
int sourceLines (loc file) {
	str fileStr = readFile(file);
	//str result = filterConsecutiveNewlines(filterComments(fileStr));
	str result = removeComments(fileStr);
	return size(split("\n", result));
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
	loc f = (getOneFrom(slocMap) | slocMap[it] > slocMap[s] ? it : s | s <- slocMap);
	println("Largest File: < f.path >. Featuring: < slocMap[f] > source lines of code.");

	// What is the total size of JPacman?
	int t = (0 | it + slocMap[s] | s <- slocMap);
	println("Total Size: < t > source lines of code, over < size(slocMap) > files.");

	// Is JPacman large according to SIG maintainability?
	
}
   
             