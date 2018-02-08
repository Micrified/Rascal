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
/*					         Location Functions						       */
/*****************************************************************************/

// Returns the path attribute of an entity.
str pathOf (Entity e, str prefix = "", str suffix = "") {
	str path ((Entity)`<{Id "."}+ ids>`) {
		return ("" | it + "<id>/" | id <- ids);
	}
	str path ((Entity)`<{Id "."}+ ids> :: <Id m>`) {
		return ("" | it + "<id>/" | id <- ids);
	}
	return prefix + path(e)[..-1] + suffix;
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

bool isDir (str ext) {
	loc l1 = |project://jpacman-framework/src/main/java/|;
	loc l2 = |project://jpacman-framework/src/test/java/|;
	l1.path = l1.path + ext;
	l2.path = l2.path + ext;
	return (isDirectory(l1) || isDirectory(l2));
}

loc findMethod (M3 m3, Entity e) {
	set[loc] m = {m | m <- methods(m3), contains(resolveLocation(m), entityToLocation(e)), contains(m, methodOf(e))};
	return resolveLocation(getOneFrom(m));
}

set[loc] toLoc (M3 m3, (Entity)`<{Id "."}+ ids> :: <Id methodName>`) {

	bool endsWithMethod (str path, str methodName) {
		set[str] matches = { match | /<match: <methodName>([^)])>/ := path };
		return size(matches) == 1;
	}
	
	str l = ("" | it + "<id>/" | id <- ids)[..-1];
	set[loc] ms = {m | m <- methods(m3), contains(resolveLocation(m).path, l), endsWithMethod(m.file, "<methodName>")};
	//return resolveLocation(getOneFrom(ms));
	return ms;
}

set[loc] packageClasses (M3 m3, loc pkg) {
	set[loc] total = elements(m3, pkg);
	set[loc] pkgs = { p | p <- total, !isClass(p) };
	return (total - pkgs | it + packageClasses(m3, p) | p <- pkgs);
}

set[loc] toLoc (M3 m3, (Entity)`<{Id "."}+ ids>`) {
	
	set[loc] packageLocations (str packageName) {
		set[loc] ps = {p | p <- packages(m3), endsWith(p.path, packageName)};
		return ({} | it + packageClasses(p) | p <- ps);
	}
	
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
  
  	void addMsgOnCondition();
  	set[loc] a = {};
  	set[loc] b = {};
  
  	switch(rule) {
  	
  		// Modality: "must".
		case (Rule)`<Entity e1> must import <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (!imports(m3, a, b)) {
				msgs += {warning("<c.path> must import <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> must depend <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (!depends(m3, a, b)) {
				msgs += {warning("<c.path> must depend on <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> must invoke <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (!invokes(m3, a, b)) {
				msgs += {warning("<c.path> must invoke <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> must instantiate <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (!instantiates(m3, a, b)) {
				msgs += {warning("<c.path> must instantiate <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> must inherit <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (!inherits(m3, a, b)) {
				msgs += {warning("<c.path> must inherit from <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		
		// Modality: "may".
		case (Rule)`<Entity e1> may import <Entity e2>` : ;
		case (Rule)`<Entity e1> may depend <Entity e2>` : ;
		case (Rule)`<Entity e1> may invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> may instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> may inherit <Entity e2>` : ;
		
		// Modality: "cannot".
		case (Rule)`<Entity e1> cannot import <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (imports(m3, a, b)) {
				msgs += {warning("<c.path> cannot import <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> cannot depend <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (depends(m3, a, b)) {
				msgs += {warning("<c.path> cannot depend on <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> cannot invoke <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (invokes(m3, a, b)) {
				msgs += {warning("<c.path> cannot invoke <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> cannot instantiate <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (instantiates(m3, a, b)) {
				msgs += {warning("<c.path> cannot instantiate <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		case (Rule)`<Entity e1> cannot inherit <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			if (inherits(m3, a, b)) {
				msgs += {warning("<c.path> cannot inherit from <d.path>", c) | c <- a, d <- b};
			}
			break;
		}
		
		// Modality: "can only".
		case (Rule)`<Entity e1> can only import <Entity e2>` : {
			a = toLoc(e1);
			b = toLoc(e2);
			//total = m3.typeDependency + m3.extends + m3....
		}
		case (Rule)`<Entity e1> can only depend <Entity e2>` : ;
		case (Rule)`<Entity e1> can only invoke <Entity e2>` : ;
		case (Rule)`<Entity e1> can only instantiate <Entity e2>` : ;
		case (Rule)`<Entity e1> can only inherit <Entity e2>` : ;
	}
  
  return msgs;
}




