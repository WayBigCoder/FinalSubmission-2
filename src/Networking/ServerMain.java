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
 * Main Server
 */
public class ServerMain {

    private ServerSocket server_socket;
    public ArrayList<String> usernames;

    //objects , which are needed for adding Thread to the queue and game start
    private final Object lock = new Object();
    private int counter = 0;
    private GameThread gameThread = null;
    private Queue<ServerThread> waitingQueue = new LinkedList<>();

    /**
     * Constructor for Main Server.
     * @throws Exception
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


    public void start() throws IOException {
        /**
         * Server will be always on, and a lot of different clients can be connected
         * For each client will be created different Thread of Server
         */
        while (true) {
            Socket socket = server_socket.accept();
            ServerThread server_thread = new ServerThread(socket, this);

            Thread thread = new Thread(server_thread);
            thread.start();
        }
    }

    /**
     * Synchronised method for Threads Clients who want to start the game
     * ---
     * This method return the same gameThread object for two first Threads in the queue.
     * 1) Counter object represents the number of Threads, who already got the same GameThread object.
     *    Since game can be created only for 2 client:
     *    ---everytime counter object reaches 2, the counter and gameThread are back to 0 and null respectively
     *    ---so if counter = 1, means that the first Thread in the waiting state has been already used for creating GameThread
     * @param serverThread
     * @return GameThread object
     */
    public GameThread addToQueue(ServerThread serverThread) {
        synchronized (lock) {
            //add Thread to the waiting queue
            waitingQueue.add(serverThread);
            while (waitingQueue.size() != 2 && counter != 1) {
                try {
                    lock.wait(); //thread 1 realize the key
                } catch (InterruptedException e) {
                    // Handle the exception
                }
            }
            if (counter == 2) {
                counter = 0;
                gameThread = null;
            }
            if (gameThread == null) {
                ServerThread sthread1 = waitingQueue.remove();
                ServerThread sthread2 = waitingQueue.remove();
                gameThread = new GameThread(sthread1, sthread2);
            }
            counter++;
            lock.notify();
            System.out.println(counter);
            return gameThread;
        }
    }




    public static void main(String[] args) {
        try {
            var server = new ServerMain();
            server.start();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }


}
