package Client;

import java.io.*;

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
