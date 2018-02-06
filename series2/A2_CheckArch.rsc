module sqat::series2::A2_CheckArch

import sqat::series2::Dicto;
import lang::java::jdt::m3::Core;
import Message;
import ParseTree;
import IO;

/*

This assignment has two parts:
- write a dicto file (see example.dicto for an example)
  containing 3 or more architectural rules for Pacman
  
- write an evaluator for the Dicto language that checks for
  violations of these rules. 

Part 1  

An example is: ensure that the game logic component does not 
depend on the GUI subsystem. Another example could relate to
the proper use of factories.   

Make sure that at least one of them is violated (perhaps by
first introducing the violation).

Explain why your rule encodes "good" design.
  
Part 2:  
 
Complete the body of this function to check a Dicto rule
against the information on the M3 model (which will come
from the pacman project). 

A simple way to get started is to pattern match on variants
of the rules, like so:

switch (rule) {
  case (Rule)`<Entity e1> cannot depend <Entity e2>`: ...
  case (Rule)`<Entity e1> must invoke <Entity e2>`: ...
  ....
}

Implement each specific check for each case in a separate function.
If there's a violation, produce an error in the `msgs` set.  
Later on you can factor out commonality between rules if needed.

The messages you produce will be automatically marked in the Java
file editors of Eclipse (see Plugin.rsc for how it works).

Tip:
- for info on M3 see series2/A1a_StatCov.rsc.

Questions
- how would you test your evaluator of Dicto rules? (sketch a design)
- come up with 3 rule types that are not currently supported by this version
  of Dicto (and explain why you'd need them). 
*/

/*****************************************************************************/
/*								Global Variables							   */
/*****************************************************************************/

// The M3 Tree.
M3 m3;


/*****************************************************************************/
/*					        Evaluation Functions							   */
/*****************************************************************************/

// Returns true if class a imports class b.
bool imports (loc a, loc b) {

	// Collect all imports (use dependencies as a workaround).
	rel[loc from, loc to] imports = {<x,y> | <x,y> <- m3.typeDependency, contains(x.path, a.path) && contains(b.path, y.path)};

	return size(imports) > 0;
}

// Returns true if class a inherits class b.
bool inherits (loc a, loc b) {
	return (<a, b> in m3.extends);
}

// Returns true if class invokes method.
bool invokes (loc classLoc, loc methodLoc) {
	return (<classLoc, methodLoc> in m3.methodInvocation);
}

// Returns true if class a depends (Invokes or inherits anything) on class b.
bool depends (loc a, loc b) {

	// Collect all class dependencies between a and b.
	rel[loc from, loc to] dependencies = {<a,b> | <a,b> <- m3.typeDependency};
	
	return (!inherits(a,b) && !invokes(a,b) && size(dependencies) == 0);
}

// Returns true if class a instantiates class b.
bool instantiates (loc a, loc b) {
	
	// Obtain calls a made to b's constructors.
	rel[loc from, loc to] constructorCalls = { <a, c> | c <- constructors(m3,b), <a, c> in m3.methodInvocation };
	
	// Return true if the relation is not empty.
	return (size(constructorCalls) > 0);
}

/*****************************************************************************/
/*					         Location Functions						       */
/*****************************************************************************/

//{Id "."}+
// | method: {Id "."}+ "::" Id

/* Converts a entity string to a loc type */
str entityToLocation (Entity e) {
	list[str] ids = [];
	
	visit (e) {
		case i: (Entity)`<Id i>`:
			ids += "<i>";
	}
	
	return (":///" | it + "<x>/" | x <- ids);
}

/*****************************************************************************/
/*					        Evaluation Functions						       */
/*****************************************************************************/

start[Dicto] arc = parse(#start[Dicto], |project://sqat-analysis/src/sqat/series2/architectureRules.dicto|);

set[Message] eval(start[Dicto] dicto, M3 m3) = eval(dicto.top, m3);

set[Message] eval((Dicto)`<Rule* rules>`, M3 m3) 
  = ( {} | it + eval(r, m3) | r <- rules );
  
set[Message] eval(Rule rule, M3 m3) {
  set[Message] msgs = {};
  
  	switch(rule) {
  	
  		// Modality: "must".
		case (Rule)`<Entity e1> must import <Entity e2>` : ;
		case (Rule)`<Entity e1> must depend <Entity e2>` : ;
		case (Rule)`<Entity e1> must invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> must instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> must inherit <Entity e2>` : ;
		
		// Modality: "may".
		case (Rule)`<Entity e1> may import <Entity e2>` : ;
		case (Rule)`<Entity e1> may depend <Entity e2>` : ;
		case (Rule)`<Entity e1> may invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> may instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> may inherit <Entity e2>` : ;
		
		// Modality: "cannot".
		case (Rule)`<Entity e1> cannot import <Entity e2>` : ;
		case (Rule)`<Entity e1> cannot depend <Entity e2>` : ;
		case (Rule)`<Entity e1> cannot invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> cannot instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> cannot inherit <Entity e2>` : ;
		
		// Modality: "can only".
		case (Rule)`<Entity e1> can only import <Entity e2>` : ;
		case (Rule)`<Entity e1> can only depend <Entity e2>` : ;
		case (Rule)`<Entity e1> can only invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> can only instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> can only inherit <Entity e2>` : ;
	}
  
  return msgs;
}




