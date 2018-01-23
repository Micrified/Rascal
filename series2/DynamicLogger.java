import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

class DynamicLogger {

    /*****************************************************/

    /** BufferedWriter Instance */
    private BufferedWriter writer;

    /** Singleton Instance */
    private static DynamicLogger instance = null;

    /*****************************************************/

    /** Writes and flushes a single line to the file */
    private void writeln (String s) {
        try {
            writer.write(s + "\n");
            writer.flush();
        } catch (IOException e) {
            System.out.println("Error: Something went wrong in writeln!");
        }
    }

    /** Writes log: 'method' invoked in 'class' */
    public void hit (String className, String methodName) {
        this.writeln(className + "," + methodName);
    }

    /** Writes log: 'statement' reached for 'method' invoked in 'class' */
    public void hit (String className, String methodName, String lineName) {
        this.writeln(className + "," + methodName + "," + lineName);
    }

    /** Returns access to the Singleton */
    public static DynamicLogger getInstance () {
        if (instance == null) {
            instance = new DynamicLogger();
        }
        return instance;
    }

    /*****************************************************/

    /** Class Initializer. */
    protected DynamicLogger () {
        try {
            FileWriter fileWriter = new FileWriter("dynlogs.csv");
            writer = new BufferedWriter(fileWriter);
        } catch (IOException e) {
            System.out.println("Error: Something went wrong in DynamicLogger constructor!");
        }
    }
}