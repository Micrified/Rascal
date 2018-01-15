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

int printReturn(str s, int c){
	println(s);
	return c;
}

/* Computes the cyclomatic complexity of a method. */
int mcc (Statement s) {
	int c = 1;
	
	visit (s) {
		/* Expressions */
		case e_infix : \infix(Expression lhs, "||", Expression rhs) :
			c = c + printReturn("infix expression ||", 1);
			
		case e_infix : \infix(Expression lhs, "&&", Expression rhs) :
			c = c + printReturn("infix expression &&", 1);
			
		/* Statements */
		case s_if : \if(Expression condition, Statement thenBranch) :
			c = c + printReturn("If Statement", 1);
			
		case s_ifElse : \if(Expression condition, Statement thenBranch, Statement elseBranch) :
			c = c + printReturn("If Else Statement", 1);
			
		case s_do : \do(Statement body, Expression condition) :
			c = c + printReturn("Do", 1);
			
		case s_forEach : \foreach(Declaration parameter, Expression collection, Statement body) :
			c = c + printReturn("For Each", 1);
			
		case s_forCond : \for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body) :
			c = c + printReturn("For Cond", 1);
			
		case s_for : \for(list[Expression] initializers, list[Expression] updaters, Statement body) :
			c = c + printReturn("For", 1);
			
		case s_label : \label(str name, Statement body) :
			c = c + printReturn("Label", 0);
			
		case s_switch : \switch(Expression expression, list[Statement] statements) :
			c = c + printReturn("Switch", 0);
		
		case s_case: \case(Expression expression) :
			c = c + printReturn("Case", 1);
			
		case s_defaultCase: \defaultCase() :
			c = c + printReturn("Default Case", 1);
			
		case s_try : \try(Statement body, list[Statement] catchClauses) :
			c = c + printReturn("Try", 1);
			
		case s_tryFinally : \try(Statement body, list[Statement] catchClauses, f : Statement \finally)  :
			c = c + printReturn("Try Finally", 1);
			
		case s_catch : \catch(Declaration exception, Statement body) :
			c = c + printReturn("Catch", 1);
			
		case s_while : \while(Expression condition, Statement body) :
			c = c + printReturn("While", 1);
	}
	return c;
}

CC cc(set[Declaration] decls) {
  CC result = {};
  
  visit (decls) {
  	case m : \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions, Statement impl) :
  		result = result + {<m.src, mcc(impl)>};
  }
  
  return result;
}

alias CCDist = map[int cc, int freq];

CCDist ccDist(CC cc) {
  // to be done
}



