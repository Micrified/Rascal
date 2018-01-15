module sqat::series1::A3_CheckStyle

import Java17ish;
import Message;
import lang::java::jdt::m3::AST;
import util::Math;
import String;
import IO;
import List;
import ParseTree;
import util::ResourceMarkers;
import util::FileSystem;

/*

Assignment: detect style violations in Java source code.
Select 3 checks out of this list:  http://checkstyle.sourceforge.net/checks.html
Compute a set[Message] (see module Message) containing 
check-style-warnings + location of  the offending source fragment. 

Plus: invent your own style violation or code smell and write a checker.

Note: since concrete matching in Rascal is "modulo Layout", you cannot
do checks of layout or comments (or, at least, this will be very hard).

JPacman has a list of enabled checks in checkstyle.xml.
If you're checking for those, introduce them first to see your implementation
finds them.

Questions
- for each violation: look at the code and describe what is going on? 
  Is it a "valid" violation, or a false positive?

Tips 

- use the grammar in lang::java::\syntax::Java15 to parse source files
  (using parse(#start[CompilationUnit], aLoc), in ParseTree)
  now you can use concrete syntax matching (as in Series 0)

- alternatively: some checks can be based on the M3 ASTs.

- use the functionality defined in util::ResourceMarkers to decorate Java 
  source editors with line decorations to indicate the smell/style violation
  (e.g., addMessageMarkers(set[Message]))

  
Bonus:
- write simple "refactorings" to fix one or more classes of violations 

*/

/* Style Violation: LineLength */

// Maximum allowed line length.
int maximumLineLength = 80;

// Maps lines to locations in a file.
list[loc] getLines (loc file) {
	list[loc] locations = [];
	
	// Convert file to string. Split into list on newline.
	list[str] lines = split("\n", readFile(file));
	
	// Iterate over lines, and compute the appropriate location.
	for (i <- index(lines)) {
		loc l = file;
		l.begin = <i+1,0>;
		l.end = <i+1, size(lines[i])>;
		locations = locations + l;
	}
	
	return locations;
}

// Checks a project for lines exceeding the maximum set line length.
set[Message] checkLineLength (loc project) {
	set[Declaration] decls = createAstsFromEclipseProject(project, true); 
	set[loc] matches = {};
	
	fs = crawl(project);
	set[Message] ms = {};
	
	// Extract all files.
	list[loc] files = [l | /file(loc l) := fs, !startsWith(l.file, "."), l.extension == "java"];
	
	// For all files, create set of new tuples combining their location with
	for (int i <- index(files)) {
		matches = matches + { l | l <- getLines(files[i]), l.end.column > maximumLineLength};
	}
	
	return ms;
}

/* Style Violation: NestedIfDepth */

// Maximum allowed nested if-statement threshold
int maximumIfDepth = 1;

// Determines the nested if-depth of a given statement.
int nestedIfDepth (Statement s) {
	int d = 0;
	
	visit (s) {
		case s_if : \if(Expression condition, Statement thenBranch) :
			d = nestedIfDepth(thenBranch) + 1;
			
		case s_ifElse : \if(Expression condition, Statement thenBranch, Statement elseBranch) :
			d = 1 + (nestedIfDepth(thenBranch) > nestedIfDepth(elseBranch) ? nestedIfDepth(thenBranch) : nestedIfDepth(elseBranch));
	}
	
	return d;
}
 
// Parses a project and filters all nested if-statements with depth larger than maximumIfDepth
set[Message] checkNestedIfStyle (loc project) {
	set[Declaration] decls = createAstsFromEclipseProject(project, true); 
	set[tuple[loc l, int d]] matches = {};
	
	visit (decls) {
		case s_if : \if(Expression condition, Statement thenBranch) :
			matches = matches + <s_if.src, nestedIfDepth(s_if)>;
  	 	case s_ifElse : \if(Expression condition, Statement thenBranch, Statement elseBranch) :
  	 		matches = matches + <s_ifElse.src, nestedIfDepth(s_ifElse)>;
  	}
  	
  	return {warning("Nested if depth of: " + toString(m.d) + " exceeds limit " + toString(maximumIfDepth) , m.l) | m <- matches, m.d > maximumIfDepth};
}

/* Style Violation: MultipleStringLiterals */

set[Message] checkStyle(loc project) {
  set[Message] result = {};
  result = checkNestedIfStyle(project);
  
  // to be done
  // implement each check in a separate function called here. 
  addMessageMarkers(result);
  return result;
}
