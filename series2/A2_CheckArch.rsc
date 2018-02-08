module sqat::series2::A2_CheckArch

import sqat::series2::Dicto;
import lang::java::jdt::m3::Core;
import Message;
import Set;
import String;
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

M3 m3 = createM3FromEclipseProject(|project://jpacman-framework|);

/*****************************************************************************/
/*					        Evaluation Functions							   */
/*****************************************************************************/

// Returns true if "from" imports everything from "to".
bool imports (M3 m3, set[loc] from, set[loc] to) {
	return (true | it && (<a,b> in m3.typeDependency) | a <- from, b <- to);
}

// Returns true if "child" inherits everything from "parent".
bool inherits (M3 m3, set[loc] child, set[loc] parent) {
	return (true | it && (<a,b> in m3.extends) | a <- child, b <- parent);
}

// Returns true if "from" invokes everything from "to".
bool invokes (M3 m3,  set[loc] from, set[loc] to) {
	return (true | it && (<a,b> in m3.methodInvocation) | a <- from, b <- to);
}

// Returns true if "a" depends (inherits | invokes | imports) from "b".
bool depends (M3 m3, set[loc] a, set[loc] b) {
	return (inherits(m3,a,b) || invokes(m3,a,b) || imports(m3,a,b));
}

// Returns true if "from" instantiates everything in "to".
bool instantiates (M3 m3, set[loc] from, set[loc] to) {
	return (true | it && (<a,b> in m3.methodInvocation) | a <- from, b <- to, isConstructor(b));
}

/*****************************************************************************/
/*					         Utility Functions						       */
/*****************************************************************************/

// Returns the path attribute of an entity.
str pathOf (Entity e) {
	str path ((Entity)`<{Id "."}+ ids>`) {
		return ("" | it + "<id>/" | id <- ids);
	}
	str path ((Entity)`<{Id "."}+ ids> :: <Id m>`) {
		return ("" | it + "<id>/" | id <- ids);
	}
	return path(e)[..-1];
}

// Returns the method attribute of an entity.
str methodOf (Entity e) {
	str method ((Entity)`<{Id "."}+ ids>`) {
		return "";
	}
	str method((Entity)`<{Id "."}+ ids> :: <Id m>`) {
		return "<m>()";
	}
	return method(e);
}

// Retruns true if the given path "ext" is a directory within main/test.
bool isDir (str ext) {
	loc l1 = |project://jpacman-framework/src/main/java/|;
	loc l2 = |project://jpacman-framework/src/test/java/|;
	l1.path = l1.path + ext;
	l2.path = l2.path + ext;
	return (isDirectory(l1) || isDirectory(l2));
}

// Locates and returns a method location best matching that of the given entity.
loc findMethod (M3 m3, Entity e) {
	set[loc] m = {m | m <- methods(m3), contains(resolveLocation(m), entityToLocation(e)), contains(m, methodOf(e))};
	return resolveLocation(getOneFrom(m));
}

// Converts a Dicto method name to a set of matching M3 locs.
set[loc] toLoc (M3 m3, (Entity)`<{Id "."}+ ids> :: <Id methodName>`) {

	// Returns true if the given "path" ends with the method call "methodName". Ignores parameters.
	bool endsWithMethod (str path, str methodName) {
		set[str] matches = { match | /<match: <methodName>([^)])>/ := path };
		return size(matches) == 1;
	}
	
	str l = ("" | it + "<id>/" | id <- ids)[..-1];
	set[loc] ms = {m | m <- methods(m3), contains(resolveLocation(m).path, l), endsWithMethod(m.file, "<methodName>")};
	return ms;
}

// Converts a Dicto package or class to a set of matching M3 locs.
set[loc] toLoc (M3 m3, (Entity)`<{Id "."}+ ids>`) {

	// Recursive function that collects all java+class locations in a package.
	set[loc] packageClasses (M3 m3, loc pkg) {
		set[loc] total = elements(m3, pkg);
		set[loc] pkgs = { p | p <- total, !isClass(p) };
		return (total - pkgs | it + packageClasses(m3, p) | p <- pkgs);
	}
	
	// Returns a set of all class locations within a package.
	set[loc] packageLocations (str packageName) {
		set[loc] ps = {p | p <- packages(m3), endsWith(p.path, packageName)};
		return ({} | it + packageClasses(m3, p) | p <- ps);
	}
	
	// Returns a set of all class locations matching a given class.
	set[loc] classLocation (str className) {
		set[loc] cs = {c | c <- classes(m3), contains(resolveLocation(c).path, className + ".java")};
		cs = cs - {nc | c <- cs, nc <- nestedClasses(m3, c)};
		return cs;
	}

	str name = ("" | it + "<id>/" | id <- ids)[..-1];
	return (isDir(name) ? packageLocations(name) : classLocation(name));
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
  set[loc] a = {}, b = {};
  //void addMsgOnCondition();
  
  
  switch(rule) {
  
  		// ******************** MODALITY: "must". ********************
  		
		case (Rule)`<Entity e1> must import <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" doesn't import "b": Place warnings in "a".
			if (!imports(m3, a, b)) {
				msgs += {warning("<c.path> must import <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> must depend <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" doesn't depend on "b": Place warnings in "a".
			if (!depends(m3, a, b)) {
				msgs += {warning("<c.path> must depend on <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> must invoke <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" doesn't invoke "b": Place warnings in "a".
			if (!invokes(m3, a, b)) {
				msgs += {warning("<c.path> must invoke <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> must instantiate <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" doesn't instantiate "b": Place warnings in "a".
			if (!instantiates(m3, a, b)) {
				msgs += {warning("<c.path> must instantiate <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> must inherit <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" doesn't inherit from "b": Place warnngs in "a".
			if (!inherits(m3, a, b)) {
				msgs += {warning("<c.path> must inherit from <d.path>", c) | c <- a, d <- b};
			}
		}
		
		// ******************** MODALITY: "may". ********************
		
		case (Rule)`<Entity e1> may import <Entity e2>` : ;	// May is optional. Do nothing.
		case (Rule)`<Entity e1> may depend <Entity e2>` : ;
		case (Rule)`<Entity e1> may invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> may instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> may inherit <Entity e2>` : ;
		
		// ******************** MODALITY: "cannot". ********************

		case (Rule)`<Entity e1> cannot import <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" imports "b": Place warnings in "a".
			if (imports(m3, a, b)) {
				msgs += {warning("<c.path> cannot import <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> cannot depend <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" depends on "b": Place warnings in "a".
			if (depends(m3, a, b)) {
				msgs += {warning("<c.path> cannot depend on <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> cannot invoke <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" invokes "b": Place warnings in "a".
			if (invokes(m3, a, b)) {
				msgs += {warning("<c.path> cannot invoke <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> cannot instantiate <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" instantiates "b": Place warnings in "a".
			if (instantiates(m3, a, b)) {
				msgs += {warning("<c.path> cannot instantiate <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> cannot inherit <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// If "a" inherits from "b": Place warnings in "a".
			if (inherits(m3, a, b)) {
				msgs += {warning("<c.path> cannot inherit from <d.path>", c) | c <- a, d <- b};
			}
		}
		
		// ******************** MODALITY: "can only". ********************
		// Intepretation: Entity e1 can only <verb> from package Entity e2.
		
		case (Rule)`<Entity e1> can only import <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// The set of imports from "a" outside "b" must be empty.
			set[loc] badImports = { importee | <importer, importee> <- m3.typeDependency, importer in a, !(importee in b) };
			
			if (size(badImports) > 0) {
				msgs += {warning("<c.path> can only import from <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> can only depend <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// A must neither inherit, invoke, or import from locations outside of b.
			set[loc] badDependencies =	{ parent | <child, parent> <- m3.extends, child in a, !(parent in b) } +
										{ invocation | <invokee, invocation> <- m3.methodInvocation, invokee in a, !(invocation in methodsOfB) } +
										{ importee | <importer, importee> <- m3.typeDependency, importer in a, !(importee in b) };
		
			if (size(badDependencies) > 0) {
				msgs += {warning("<c.path> can only depend on <d.path>", c) | c <- a, d <- b};
			}
		}
		case (Rule)`<Entity e1> can only invoke <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// The set of invocations of "a" to methods outside of "b" must be empty.
			set[loc] methodsOfB = ( {} | it + methods(m3, c) | c <- b );
			set[loc] badInvocations = { invocation | <invokee, invocation> <- m3.methodInvocation, invokee in a, !(invocation in methodsOfB) };
			
			if (size(badInvocations) > 0) {
				msgs += {warning("<c.path> can only invoke from <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> can only instantiate <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// The set of instantiations in "a" to classes outside "b" must be empty. 
			set[loc] badInstantiations = { instantiation | <instantiator, instantiation> <- m3.methodInvocation, instantiator in a, isConstructor(instantiation), !(instantiation in b) };
			
			if (size(badInstantiations) > 0) {
				msgs += {warning("<c.path> can only instantiate from <d.path>", c) | c <- a, d <- b};
			}
		}
		
		case (Rule)`<Entity e1> can only inherit <Entity e2>` : {
			a = toLoc(m3, e1); b = toLoc(m3, e2);
			
			// The set of classes "a" inherits from, that are not in "b", must not be empty. 
			set[loc] badInheritances = { parent | <child, parent> <- m3.extends, child in a, !(parent in b) };
			
			if (size(badInheritances) > 0) {
				msgs += {warning("<c.path> can only inherit from <d.path>", c) | c <- a, d <- b};
			}
		}
	}
  
  return msgs;
}

set[Message] a2 (loc project) {
	
	// Initialize the M3 object.
	M3 m3 = createM3FromEclipseProject(project);
	
	// Initialize the rules.
	start[Dicto] rules = parse(#start[Dicto], |project://sqat-analysis/src/sqat/series2/architectureRules.dicto|);
	
	// Evaluate the rules.
	set[Message] messages = eval(rules, m3);
	
	// Answer questions.
	println("How would you test your evaluator of Dicto rules?");
	println("- To test our evaluator, we would simple construct a series of sets that can be used to assess every possible constaint allowed in the grammar.");
	
	println("Come up with 3 rule types that are not currently supported by this version of Dicto (and explain why you\'d need them).");
	println("-");
	
	return messages;
}



