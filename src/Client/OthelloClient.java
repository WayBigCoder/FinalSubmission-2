package Client;

import java.io.IOException;
import java.net.InetAddress;

/**
 * This interface of an Othello client.
 */
public interface OthelloClient {
    /**
     * Connects to the specified server address and port.
     *
     * @param address The InetAddress of the server
     * @param port    The port number
     * @return true if the connection is successful, false otherwise
     * @throws IOException if an error occurs while establishing the connection
     */
    boolean connect(InetAddress address, int port) throws IOException;

    /**
     * Closes the connection between the server and the client.
     */
    void close();
}
