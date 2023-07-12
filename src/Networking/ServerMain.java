package Networking;

import java.io.IOException;
import java.net.BindException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Scanner;

/**
 * Main Server class that handles client connections and game initialization.
 */
public class ServerMain {

    private ServerSocket server_socket;
    public ArrayList<String> usernames;

    // Objects needed for adding Thread to the queue and game start
    private final Object queueLock = new Object();
    // Counter object represents the number of Threads, who already got the same GameThread object.
    private int threadCounter = 0;
    private GameThread gameThread = null;
    private Queue<ServerThread> waitingQueue = new LinkedList<>();

    /**
     * Constructor for the Main Server.
     *
     * @throws Exception if an error occurs during server initialization.
     */
    public ServerMain() throws Exception {
        int port;

        while (true) {
            try {
                Scanner sc = new Scanner(System.in);
                System.out.print("Choose port for server: ");
                port = sc.nextInt();

                if (port > 1 && port < 65534) {
                    try {
                        server_socket = new ServerSocket(port);
                        break;
                    } catch (BindException e) {
                        System.out.println("Port already in use. Please choose a different port.");
                    }
                } else {
                    System.out.println("Invalid port");
                }

            } catch (Exception error) {
                System.out.println("Write a real port number!");
            }
        }

        waitingQueue = new LinkedList<>();
        usernames = new ArrayList<>();
        System.out.println("Port " + port + " is now open");
    }

    /**
     * Starts the server and listens for client connections.
     *
     * @throws IOException if an error occurs during socket acceptance.
     */
    public void start() throws IOException {
        /*
         * The server will be always on, and multiple different clients can be connected.
         * For each client, a separate ServerThread will be created.
         */
        while (true) {
            Socket socket = server_socket.accept();
            ServerThread server_thread = new ServerThread(socket, this);

            Thread thread = new Thread(server_thread);
            thread.start();
        }
    }

    /**
     * Synchronised method for Threads Clients who want to start the game.
     * ---
     * This method returns single GameThread object for the first two Threads in the queue.
     *
     * @param serverThread The ServerThread object to be added to the queue.
     * @return The GameThread object used for the current game.
     */
    public GameThread addToQueue(ServerThread serverThread) {
        synchronized (queueLock) {
            //add Thread to the waiting queue
            waitingQueue.add(serverThread);
            // If the counter is 1, it means that the first Thread in the waiting state has already been used for creating GameThread.
            while (waitingQueue.size() != 2 && threadCounter != 1) {
                try {
                    queueLock.wait(); // Thread 1 releases the lock
                } catch (InterruptedException e) {
                    // Handle the exception
                }
            }

            /*
             * Since game can be created only for 2 client:
             * everytime counter object reaches 2, the counter and gameThread are back to 0 and null respectively
             */
            if (threadCounter == 2) {
                threadCounter = 0;
                gameThread = null;
            }
            if (gameThread == null) {
                ServerThread sthread1 = waitingQueue.remove();
                ServerThread sthread2 = waitingQueue.remove();
                gameThread = new GameThread(sthread1, sthread2);
            }
            threadCounter++;
            queueLock.notify();
            System.out.println(threadCounter);
            return gameThread;
        }
    }

    /**
     * Main entry point of the server application.
     *
     * @param args The command-line arguments.
     */
    public static void main(String[] args) {
        try {
            var server = new ServerMain();
            server.start();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }


}
