package test;

import Networking.ServerMain;
import org.junit.jupiter.api.*;

import java.io.*;
import java.net.Socket;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Class of tests for the server functionality.
 */
public class ServerTest {
    private static ServerMain server;
    private static int port;
    private Socket clientSocket;

    /**
     * Sets up the server before all tests.
     *
     * @throws Exception if an error occurs during setup.
     */
    @BeforeAll
    public static void setUpClass() throws Exception {
        // Set up the server
        port = 12345;
        server = new ServerMain(port);

        // Start server as separate thread
        Thread serverThread = new Thread(() -> {
            try {
                server.start();
            } catch (IOException e) {
                e.printStackTrace();
            }
        });
        serverThread.start();
    }

    /**
     * Stops the server after all tests.
     *
     * @throws IOException if an error occurs while stopping the server.
     */
    @AfterAll
    public static void tearDownClass() throws IOException {
        server.stop();
    }

    /**
     * Sets up client which will be connected to the Server.
     *
     * @throws Exception if an error occurs during setup.
     */
    @BeforeEach
    public void setUp() throws Exception {
        // Wait for the server to start
        Thread.sleep(1000);

        // Connect client to server
        clientSocket = new Socket("localhost", port);
    }

    /**
     * Cleans up after each test.
     *
     * @throws IOException if an error occurs.
     */
    @AfterEach
    public void tearDown() throws IOException {
        clientSocket.close();
    }

    /**
     * Tests the login functionality of the server.
     *
     * @throws IOException if an error occurs.
     */
    @Test
    public void testLogin() throws IOException {
        // input/output streams for client
        BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
        PrintWriter out = new PrintWriter(new OutputStreamWriter(clientSocket.getOutputStream()), true);

        // Send the LOGIN message
        out.println("LOGIN~Alice");

        // Read the response from the server
        String response = in.readLine();

        // Check if server response LOGIN
        assertEquals("LOGIN", response);
    }

    /**
     * Tests the error handling of the server.
     *
     * @throws IOException if an error occurs.
     */
    @Test
    public void testError() throws IOException {
        // input/output streams for client
        BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
        PrintWriter out = new PrintWriter(new OutputStreamWriter(clientSocket.getOutputStream()), true);

        // Send the LOGIN message 2 times
        out.println("LOGIN~Bob");
        out.println("LOGIN~Sara");

        String response = in.readLine();

        // Check if first result is LOGIN
        assertEquals("LOGIN", response);

        // Send wrong message to the server
        out.println("RandomMessage");
        // Read the response from the server
        response = in.readLine();

        // Send the QUEUE message
        out.println("QUEUE~Bob");

        // Check if the response is ERROR, because wrong message was sent
        assertEquals("ERROR", response);
    }

    /**
     * Tests game initialization when 2 players are connected
     *
     * @throws IOException if an error occurs.
     */
    @Test
    public void testGame() throws IOException {
        // input/output streams for client
        BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
        PrintWriter out = new PrintWriter(new OutputStreamWriter(clientSocket.getOutputStream()), true);

        // Send the LOGIN message for player 1
        out.println("LOGIN~Player1");
        String response = in.readLine();

        // Check if the response is LOGIN
        assertEquals("LOGIN", response);

        // Send the QUEUE message for player 1
        out.println("QUEUE");

        // Read the response from the server
        response = in.readLine();

        // Check if the response is correct
        assertEquals("NEWGAME~Bob~Player1", response);
    }

    /**
     * Tests the disconnect functionality of the server.
     * Checks also whether username of disconnected player was deleted
     *
     * @throws IOException if an error occurs.
     */
    @Test
    public void testDisconnect() throws IOException, InterruptedException {
        // input/output streams for client
        BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
        PrintWriter out = new PrintWriter(new OutputStreamWriter(clientSocket.getOutputStream()), true);

        // Send the LOGIN message
        out.println("LOGIN~Charlie");
        String response = in.readLine();

        // Check if the response is LOGIN
        assertEquals("LOGIN", response);

        // Disconnect client
        clientSocket.close();


        ArrayList<String> usernames = server.usernames;
        System.out.println(server.usernames);

        // Wait 1 second to make sure name is deleted
        Thread.sleep(1000);

        // Check if the username is removed from the server's list
        // it should be 0, as only Charlie was connected to server
        assertEquals(0, usernames.size());
    }
}
