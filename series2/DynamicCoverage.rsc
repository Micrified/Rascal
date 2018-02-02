module sqat::series2::DynamicCoverage

import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import IO;
import List;
import ParseTree;
import util::FileSystem;
import String;
import Set;
import Java17ish;

// Helper function to deal with concrete statement lists
// second arg should be a closure taking a location (of the element)
// and producing the BlockStm to-be-inserted 
BlockStm* putAfterEvery(BlockStm* stms, BlockStm(loc) f) {
  
  Block put(b:(Block)`{}`) = (Block)`{<BlockStm s>}`
    when BlockStm s := f(b@\loc);
  
  Block put((Block)`{<BlockStm s0>}`) = (Block)`{<BlockStm s0> <BlockStm s>}`
    when BlockStm s := f(s0@\loc);
  
  Block put((Block)`{<BlockStm s0> <BlockStm+ stms>}`) 
    = (Block)`{<BlockStm s0> <BlockStm s> <BlockStm* stms2>}`
    when
      BlockStm s := f(s0@\loc), 
      (Block)`{<BlockStm* stms2>}` := put((Block)`{<BlockStm+ stms>}`);

  if ((Block)`{<BlockStm* stms2>}` := put((Block)`{<BlockStm* stms>}`)) {
    return stms2;
  }
}

start[CompilationUnit] instrumentClass (loc classLoc) {
	
	// Construct the parse tree for the class.
	start[CompilationUnit] parseTree = parseJava(classLoc);
	
	// Construct an instrumented method call.
	BlockStm instrumentMethod (loc methodLoc) {
		return parse(#BlockStm, "DynamicLogger.getInstance().hit(\"<classLoc>\", \"<methodLoc>\");");
	}
	
	// Constuct an instrumented statement call.
	BlockStm instrumentLine (loc methodLoc, loc lineLoc) {
		return parse(#BlockStm, "DynamicLogger.getInstance().hit(\"<classLoc>\", \"<methodLoc>\", \"<lineLoc>\");");
	}
	
	/* Perform subtree replacement with => */
	parseTree = visit (parseTree) {
		case (MethodDec)`<MethodDecHead h> {<BlockStm* b>}` => (MethodDec)`<MethodDecHead h> {<BlockStm h2> <BlockStm* b2>}`
		  when 
		  	BlockStm* b2 := putAfterEvery(b, BlockStm (loc lineLoc) { return instrumentLine (h@\loc, lineLoc); }),
		  	BlockStm h2 := instrumentMethod(h@\loc)
	}
	
	return parseTree;
}

void gitsome (loc project, str shadow) {
	for(f <- files(project), f.extension == "java") {
		start[CompilationUnit] newclass = instrumentClass(f);
		f.authority = shadow;
		writeFile(f, newclass);
	}
}
