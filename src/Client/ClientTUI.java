package Client;

import java.io.*;

/**
 * This class represents a Client Text User Interface (TUI) for handling input and output.
 */
public class ClientTUI {
    public BufferedReader in;
    public PrintWriter out;

    /**
     * Constructor that initializes a new BufferedReader and a PrintWriter
     */
    public ClientTUI() {
        in = new BufferedReader(new InputStreamReader(System.in));
        out = new PrintWriter(System.out);
    }
}
