module sqat::series1::A2_McCabe

import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;

/*

Construct a distribution of method cylcomatic complexity. 
(that is: a map[int, int] where the key is the McCabe complexity, and the value the frequency it occurs)


Questions:
- which method has the highest complexity (use the @src annotation to get a method's location)

- how does pacman fare w.r.t. the SIG maintainability McCabe thresholds?

- is code size correlated with McCabe in this case (use functions in analysis::statistics::Correlation to find out)? 
  (Background: Davy Landman, Alexander Serebrenik, Eric Bouwers and Jurgen J. Vinju. Empirical analysis 
  of the relationship between CC and SLOC in a large corpus of Java methods 
  and C functions Journal of Software: Evolution and Process. 2016. 
  http://homepages.cwi.nl/~jurgenv/papers/JSEP-2015.pdf)
  
- what if you separate out the test sources?

Tips: 
- the AST data type can be found in module lang::java::m3::AST
- use visit to quickly find methods in Declaration ASTs
- compute McCabe by matching on AST nodes

Sanity checks
- write tests to check your implementation of McCabe

Bonus
- write visualization using vis::Figure and vis::Render to render a histogram.

*/

set[Declaration] jpacmanASTs() = createAstsFromEclipseProject(|project://jpacman-framework|, true); 
set[Declaration] fileASTs() = createAstsFromFiles({|project://sqat-analysis/src/sqat/series1/MapParser.java|}, true);

alias CC = rel[loc method, int cc];


/* Computes the cyclomatic complexity of a method. */
int mcc (Statement s) {
	int c = 1;
	
	visit (s) {
		/* Expressions */
		case e_infix: 		\infix(_, "||", _) :
			c = c + 1;
			
		case e_infix: 		\infix(_, "&&", _) :
			c = c + 1;
			
		/* Statements */
		case s_if: 			\if(_, _) :
			c = c + 1;
			
		case s_ifElse: 		\if(_,_,_) :
			c = c + 1;
			
		case s_do: 			\do(_,_) :
			c = c + 1;
			
		case s_forEach: 		\foreach(_,_,_) :
			c = c + 1;
			
		case s_forCond: 		\for(_,_,_,_) :
			c = c + 1;
			
		case s_for: 			\for(_,_,_) :
			c = c + 1;
			
		case s_label: 		\label(_,_) :
			c = c + 1;
			
		case s_switch: 		\switch(_, _) :
			c = c + 1;
		
		case s_case: 		\case(_) :
			c = c + 1;
			
		case s_defaultCase:	\defaultCase() :
			c = c + 1;
			
		case s_try : 		\try(_,_) :
			c = c + 1;
			
		case s_tryFinally: 	\try(_,_,_)  :
			c = c + 1;
			
		case s_catch: 		\catch(_,_) :
			c = c + 1;
			
		case s_while: 		\while(_,_) :
			c = c + 1;
	}
	
	return c;
}

CC cc(set[Declaration] decls) {
  CC result = {};
  
  visit (decls) {
  	case m : \method(_, _, _, _, Statement impl) :
  		result = result + {<m.src, mcc(impl)>};
  }
  
  return result;
}

alias CCDist = map[int cc, int freq];

CCDist ccDist(CC cc) {
  // to be done
}



