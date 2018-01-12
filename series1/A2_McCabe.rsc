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

/* Returns 1 if the given string operator is a comparator */
int isBooleanOperator (str op) {
	if ((op == "\>") || (op == "\>=") || (op == "==") || 
		(op == "\<=") || (op == "\<") || (op == "!=") || 
		(op == "||") || (op == "&&")) {
		return 1;
	}
	return 0;
}

/* Computes cyclomatic complexity of an expression */
int ecc (Expression e) {
	int c = 0;
	visit (e) {
		case e_infix : \infix(Expression lhs, str operator, Expression rhs) :
			c = c + isBooleanOperator(operator) + ecc(lhs) + ecc(rhs);
		case e_conditional : \conditional(Expression expression, Expression thenBranch, Expression elseBranch) :
			c = c + ecc(expression) + ecc(thenBranch) + ecc(elseBranch);
	}
	return c;
}


/* Computes the cyclomatic complexity of a method */
int mcc (Statement s) {
	int c = 0;
	
	visit (s) {
		case s_if : \if(Expression condition, Statement thenBranch) :
			c = c + 1 + ecc(condition) + mcc(thenBranch);
			
		case s_ifElse : \if(Expression condition, Statement thenBranch, Statement elseBranch) :
			c = c + 2 + ecc(condition) + mcc(thenBranch) + mcc(elseBranch);
			
		case s_do : \do(Statement body, Expression condition) :
			c = c + 1 + ecc(condition) + mcc(body);
			
		case s_forEach : \foreach(Declaration parameter, Expression collection, Statement body) :
			c = c + 1 + mcc(body);
			
		case s_forCond : \for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body) :
			c = c + 1 + ecc(condition) + ( 0 | it + ecc(k) | k <- initializers ) + ( 0 | it + ecc(k) | k <- updaters) + mcc(body);
			
		case s_for : \for(list[Expression] initializers, list[Expression] updaters, Statement body) :
			c = c + 1 + ( 0 | it + ecc(k) | k <- updaters) + mcc(body);
			
		case s_label : \label(str name, Statement body) :
			c = c + mcc(body);
			
		case s_switch : \switch(Expression expression, list[Statement] statements) :
			c = c + 1 + ecc(expression) + ( 0 | it + mcc(k) | k <- statements );
			
		case s_syncStatement : synchronizedStatement(Expression lock, Statement body) :
			c = c + 1 + ecc(lock) + mcc(body);
			
		case s_try : \try(Statement body, list[Statement] catchClauses) :
			c = c + 1 + mcc(body) + ( 0 | it + mcc(k) | k <- catchClauses );
			
		case s_tryFinally : \try(Statement body, list[Statement] catchClauses, f : Statement \finally)  :
			c = c + 1 + mcc(body) + ( 0 | it + mcc(k) | k <- catchClauses) + mcc(f);
			
		case s_catch : \catch(Declaration exception, Statement body) :
			c = c + mcc(body);
			
		case s_while : \while(Expression condition, Statement body) :
			c = c + ecc(condition) + mcc(body);
	}
	return c;
}

CC cc(set[Declaration] decls) {
  CC result = {};
  
  visit (decls) {
  	case m : \method(Type \return, str name, list[Declaration] parameters, list[Expression] exceptions, Statement impl) :
  		result = result + {<m.src, 1 + mcc(impl)>};
  }
  
  return result;
}

alias CCDist = map[int cc, int freq];

CCDist ccDist(CC cc) {
  // to be done
}



