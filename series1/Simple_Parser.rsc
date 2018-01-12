module sqat::series1::Simple_Parser

import IO;
import ParseTree;
import String;
import util::FileSystem;

/* Garbage 
	lexical NewLineSeq 		= ^"\n" [\n]*;
	
	
	lexical BlocStart		= "/*";
	
	lexical BlocEnd			= "*/";
	
	lexical LineComment		= ^"//" (![\n])* "\n";
*/

lexical Id = [a-zA-Z]+ [0-9]*;

lexical Eq = "\>" | "\>=" | "==" | "\<" | "\<=" | "!=";

lexical Num = [0-9]+;

syntax Comparison = Id Eq Num ";" ;
syntax Assignment = Id "=" Num ";" ;
syntax Expression = Comparison | Assignment;
syntax ExpressionList = Expression*;

 int countAssignments (str input) {
 	int count = 0;

 	pt = parse(#ExpressionList, input);
 	visit (pt) {
 		case Assignment c:
 			count = count + 1;
 	}
 	return count; 
 }