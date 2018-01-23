module sqat::Intro

import util::FileSystem;

int main() {
    loc jpacman = |project://jpacman-framework/src|;

    /* Read files with crawl(er?) */
    crawl(jpacman);

    /* Crawl takes a location and returns a fileSystem */
    // FileSystem crawl(loc l) = isDirectory(l) ? directory(l) ...

    fs = crawl(jpacman);

    return bestCountDirs(fs);
}

int countDirs(FileSystem fs) {
	switch (fs) {
		case directory(loc l, set[FileSystem] kids): {
			int subDirectoryCount = 0;
			
			for (FileSystem kid <- kids) {
				subDirectoryCount += countDirs(kid);
			}
			
			return subDirectoryCount + 1;
		}
		
		case file(_):
			return 0;
	}
}

int betterCountDirs(FileSystem fs) {
	// Switch with built in recursion??
	// d:directory(..) binds directory to d. Can do d.l or something after.
	int count = 0;
	visit (fs) {
		case directory(_, _): {
			count += 1;
		}
	}
	return count;
}

// Start with 0, and add 1 to 'it' (current value) each time you match a directory.
// Forward slash means at arbitrary depth in the filesystem, you match a directory in
// the file system. Operator := is a matching operating for an expression.
// := "Match LHS pattern against RHS value. Works on tree-like structures".
// Will work on a set of filesystems too. Can traverse each element of the set at arbitrary depth.

int bestCountDirs(FileSystem fs) = ( 0 | it + 1 | /directory(_, _) := fs);

// Another example of using forward slash to pattern match.
// for (/directory(_,_) := fs) { count += 1 }


// Basic data types.
int exploreSets () {
	
	xs = {1,2,3,4};		// Set of integers.
	ys = {<1,2>, <3,4>};	// Set of integer tuples.
	zs = [1..10];		// 
	
	ms = (1:2,2:3);
	
	//int incr(int n) = n + 1;
	// [incr(i) | i <- lst]
	
	
	return 0;
}

// Use break with visit to avoid visiting deeper subtrees. Parse is bottom up, left to right.
// Find all methods, and then find the cyclomatic complexity of said methods.



/* Examples */

// Use lexical to define things you want to match.
lexical Comment 
	= "/*" CommentChar* "*/"
	
lexical lineComment
	= "//"

alias SLOC = map[loc files, int sloc];

map[str, int] slocDist(SLOK sloc, str(int) ??) {

}

// Example test. Single quote allows you to write the string such that it contains implicit newlines.
// I.E: The following has two newlines. Visit .source, and .declaration to find structure of 
test bool commentsTest() =
	sloc("a
		 '/"
		 ' new line
		 ' */
		 'b;") == 2;
		 
// Will need data 

int sloc (str sec, loc sth = |file://dummy()|) {
	pt = parse(...);
	
	for (Token t <- pt.tokens) {
		switch(t) {
			case (Token)' <Comment c>:
			
		}
	}
}

SLOC sloc(loc project) {
	
}