module sqat::series1::A1_SLOC

import IO;
import ParseTree;
import Boolean;
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
	str result = filterConsecutiveNewlines(filterComments(fileStr));
	return size(split("\n", result));
}

/* Returns mapping: Files to Lines-Of-Code */
SLOC sloc (loc project) {
	fs = crawl(project);
	SLOC result = (l : sourceLines(l) | /file(loc l) := fs, !startsWith(l.file, "."), l.extension == "java");
	int totalLines = ( 0 | it + result[k] | k <- result );
	printExp("Total SLOC = ", totalLines); print("\n");
	return result;
}

   
             