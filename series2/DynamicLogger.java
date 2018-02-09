package nl.tudelft;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.Set;
import java.util.HashSet;

public class DynamicLogger {

    /*****************************************************/
	
	/** Statement buffer (avoids duplicate statements) */
	private Set<String> lineBuffer, methodBuffer;

    /** BufferedWriter Instance */
    private BufferedWriter lineWriter, methodWriter;

    /** Singleton Instance */
    private static DynamicLogger instance = null;

    /*****************************************************/

    /** Writes and flushes a single line to the file */
    private void writeln (String s, BufferedWriter w)  {
    		try {
            w.write(s + "\n");
            w.flush();
        } catch (IOException e) {
            System.out.println("Error: Something went wrong in writeln!");
        } 
    	}

    /** Writes log: 'method' invoked in 'class' */
    public void hit (String className, String methodName)  {
		String s = className + "&" + methodName; 
		if (!methodBuffer.contains(s)) {
			writeln(s, methodWriter);
			methodBuffer.add(s);
		} 
    }
    
    /** Writes log: 'statement' reached for 'method' invoked in 'class' */
    public void hit (String className, String methodName, String lineName)  {
		String s = className + "&" + methodName + "&" + lineName;
		if (!lineBuffer.contains(s)) {
			writeln(s, lineWriter);
			lineBuffer.add(s);
		}
    	}

    /** Returns access to the Singleton */
    public static DynamicLogger getInstance ()  {
    		if (instance == null) {
            instance = new DynamicLogger();
        }
    		return instance;
    	}

    /*****************************************************/

    /** Class Initializer. */
    protected DynamicLogger () {
        try {
        	
        		// Initialize buffer to avoid duplicates.
        		this.lineBuffer = new HashSet<String>();
        		this.methodBuffer = new HashSet<String>();
        		
        		// Initialize FileWriters.
        		FileWriter lineFileWriter = new FileWriter("dynLineLogs.csv");
        		FileWriter methodFileWriter = new FileWriter("dynMethodLogs.csv");
        		
        		// Initialize BufferedWriters.
        		this.lineWriter = new BufferedWriter(lineFileWriter);
        		this.methodWriter = new BufferedWriter(methodFileWriter);
        		
        } catch (IOException e) {
            System.out.println("Error: Something went wrong in DynamicLogger constructor!");
        }
    }
}