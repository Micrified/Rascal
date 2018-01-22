module sqat::series1::A2_McCabe

import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;
import util::Math;
import Map;
import Set;
import String;
import analysis::statistics::Correlation;
import sqat::series1::A1_SLOC;

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

/* Test for an empty method */
set[Declaration] complexityTestFile_1 = createAstsFromFiles({|project://sqat-analysis/src/sqat/series1/A2_Tests/A2_McCabe_ComplexityTest_1.java|}, true); 
test bool complexityTest1() = 
	getMaxCC(cc(complexityTestFile_1)).cc == 1;

/* Test for method of known complexity */
set[Declaration] complexityTestFile_2 = createAstsFromFiles({|project://sqat-analysis/src/sqat/series1/A2_Tests/A2_McCabe_ComplexityTest_2.java|}, true);
test bool complexityTest2() = 
	getMaxCC(cc(complexityTestFile_2)).cc == 6;

/* Computes the cyclomatic complexity of a method. */
int mcc (Statement s) {
	int c = 1;
	
	visit (s) {
		/* Expressions */
		case \infix(_, "||", _) :
			c += 1;
			
		case \infix(_, "&&", _) :
			c += 1;
			
		/* Statements */
		case \if(_, _) :
			c += 1;
			
		case \if(_,_,_) :
			c += 1;
			
		case \do(_,_) :
			c += 1;
			
		case \foreach(_,_,_) :
			c += 1;
			
		case \for(_,_,_,_) :
			c += 1;
			
		case \for(_,_,_) :
			c += 1;
			
		case \label(_,_) :
			c += 1;
		
		case \case(_) :
			c += 1;
			
		case \defaultCase() :
			c += 1;
			
		case \try(_,_) :
			c += 1;
			
		case \try(_,_,_)  :
			c += 1;
			
		case \catch(_,_) :
			c += 1;
			
		case \while(_,_) :
			c += 1;
	}
	
	return c;
}

/* Computes the cyclomatic-complexity for a M3 Project AST */
CC cc(set[Declaration] decls) {
  CC result = {};
  
  visit (decls) {
  	case m : \method(_, _, _, _, Statement impl) :
  		result = result + {<m.src, mcc(impl)>};
  }
  
  return result;
}

alias CCDist = map[int cc, int freq];

/* Returns the method with the highest cyclomatic complexity. */
tuple[loc method, int cc] getMaxCC (CC cc) {
	return (getOneFrom(cc) | (it.cc > next.cc ? it : next) | next <- cc);
}

/* Computes a distribution for a cyclomatic complexity relation */
CCDist ccDist(CC cc) {
	
	/* 1) Retrieve method with highest cyclomatic complexity. */
	tuple [loc bestMethod, int maxCC] m = getMaxCC(cc);
	
	/* 2)  Initialize histogram */
	CCDist histogram = (complexity : 0| complexity <- [1..(m.maxCC + 1)] );
	
	/* 3) Compute frequency distribution */
	for (<loc _, int c> <- cc) {
		histogram[c] = histogram[c] + 1;
	}
	
	return histogram;
}

/* Prints two types of correlations */
void slocCCCorrelation (CC cc) {
	lrel[int sourceLines, int complexity] x = [<sourceLines(m), c> | <loc m, int c> <- cc];
	println("\t\tPearsons Correlation: <PearsonsCorrelation(x)>");
	println("\t\tSpearmans Correlation: <SpearmansCorrelation(x)>");
}

void a2 () {

	println("***************************** A2_MCCABE: RESULTS *********************************"); 
	println("FACTS:");
	
	// 1. Compute Cyclomatic Complexities.
	CC projectComplexity = cc(jpacmanASTs());
	CC projectWithoutTestComplexity = {<method,complexity> | <method,complexity> <- projectComplexity, !contains(method.path, "/test") };
	
	// 2. Extacting method with highest complexity.
	tuple [loc methodName, int methodCC] m = getMaxCC(projectComplexity);
	println("\tMethod of highest complexity:\n\t\t<m.methodName>");
	println("\n\tComplexity of this method is: <m.methodCC>");
	println("\n\tComplexity histogram: <ccDist(projectComplexity)>");
	
	println("QUESTIONS:");
	
	// 3. Project score with respect to McCabe SIG Maintainability threshold.
	println("\tSIG Maintainability Threshold Table:");
	println("\t\tBecause the highest cyclomatic-complexity score for a method is 8, we can say that");
	println("\t\tall methods will be given a risk evaluation of \"simple, without much risk\"");
	println("\t\tThe corresponding ranking is thus \"++\".");
	
	// 4. Assessing the correlation between cyclomatic complexity and source lines of code.
	println("\n\tIs code size correlated with cyclomatic complexity?");
	slocCCCorrelation(projectComplexity);
	println("\tThe results indicate that there exists a considerably positive correlation");
	println("\tbetween the cyclomatic complexity and number of source lines of code.");
	
	// 5. Assessing the correlation, but without including tests.
	println("\n\tWhat is the correlation without including the test files?");
	slocCCCorrelation(projectWithoutTestComplexity);
	println("\n\tWe can see that removing the tests has increased the correlation in both correlators.");
	
	println("\nTESTS:");
	
	// Print test results.
	println("\tComplexity Test on Basic Method:\t <complexityTest1() ? "PASSED" : "FAILED" >");
	println("\tComplexity Test on Complex Method:\t <complexityTest2() ? "PASSED" : "FAILED" >");
	
}
