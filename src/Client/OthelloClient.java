package Client;

import java.io.IOException;
import java.net.InetAddress;

public interface OthelloClient {
    /**
     * The boolean methods should return true on success or false on failure, for example when the
     connection is broken
     */
    boolean connect(InetAddress address, int port) throws IOException;

    /**
     * This method should close the connection between the server and client
     */
    void close();
}
