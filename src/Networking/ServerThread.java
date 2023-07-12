package Networking;

import GameLogic.AbstractPlayer;
import java.io.*;
import java.net.Socket;
import util.Protocol;

/**
 * This class represents a thread that handles communication with a client.
 * Each instance of this class is responsible for one client connection.
 */
public class ServerThread implements Runnable {
    private Socket socket;
    private ServerMain serverMain;
    private GameThread gameThread;
    private String name;

    /**
     * Constructs a new ServerThread object.
     *
     * @param socket      The socket representing the client connection
     * @param serverMain  The main server object
     */
    public ServerThread(Socket socket, ServerMain serverMain) {
        this.socket = socket;
        this.serverMain = serverMain;
    }

    /**
     * Returns the name associated with this client thread.
     *
     * @return The name of the client
     */
    public String getName() {
        return name;
    }



    /**
     * Checks whether the client, which turn it is, sends the MOVE message.
     * Only MOVE~INDEX messages are accepted when it is the client's turn.
     *
     * @param message of ServerThread who's turn it is
     * @param out_socket PrintWriter for sending messages to the client
     * @return boolean Indicates whether the move message was accepted or not
     */
    private boolean checkMoveMessage(String message, PrintWriter out_socket) {
        if (message.startsWith("MOVE")) {
            String[] parse = message.split("~");
            gameThread.moveIndex = Integer.parseInt(parse[1]);
            gameThread.makeMove();
            out_socket.println(Protocol.moveFromClient(gameThread.moveIndex));
            return true;
        } else {
            out_socket.println("ERROR");
            return false;
        }
    }

    @Override
    public void run() {
        try {
            System.out.println("New client has connected!:)");

            // Incoming message reader
            BufferedReader in_socket = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            // Outgoing message writer
            PrintWriter out_socket = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true);

            String message;

            // HANDSHAKE
            while (true) {
                // Read message from client side
                message = in_socket.readLine();
                if (message == null) {
                    System.out.println("Client has disconnected.");
                    // Close the socket if Client has disconnected
                    socket.close();
                    System.out.println("Disconnected from client.");
                    break;
                }
                if (message.startsWith("HELLO")) {
                    out_socket.println(Protocol.helloFromServer("Ammar"));

                } else if (message.startsWith("LOGIN")) {
                    String[] parse = message.split("~");
                    name = parse[1];

                    if (serverMain.usernames.contains(name)) {
                        out_socket.println(Protocol.alreadyLoggedInFromServer());
                    } else {
                        serverMain.usernames.add(name);
                        out_socket.println(Protocol.loginFromServer());
                        break;
                    }
                } else {
                    out_socket.println("ERROR");
                }
            }

            // MAIN COMMANDS
            while (true) {
                message = in_socket.readLine();

                if (message == null) {
                    // Close the socket if the message is null
                    socket.close();
                    System.out.println("Disconnected from clientt.");
                    if (name != null) {
                        serverMain.usernames.remove(name);
                    }
                    break;

                } else if (message.startsWith("LIST")) {
                    out_socket.println(Protocol.listFromServer(serverMain.usernames));

                } else if (message.startsWith("QUEUE")) {
                    // As soon as this command is called, the game loop is started
                    // The code can be paused here as the Thread can be in wait() state in the AddToQueue method
                    gameThread = serverMain.addToQueue(this);
                    // Send Protocol message to Clients about a new game
                    out_socket.println(Protocol.newGameFromServer(gameThread.name1(), gameThread.name2()));

                    while (!gameThread.isGameOver()) {
                        // If it is the turn of the client with the matching name
                        // and both players are still alive
                        if (gameThread.nameForTurn().equals(name) && gameThread.getGame().getBothPlayerAlive()) {

                            // If client, whose turn it is, doesn't have valid moves
                            if (gameThread.getGame().getValidMoves().size() == 0) {
                                gameThread.getGame().turnIndexChange();
                                // If count reaches two, means two players don't have valid moves
                                gameThread.getGame().incrementTurnsWithoutMove();
                                out_socket.println(Protocol.moveFromClient(64));
                                gameThread.moveIndex = 64;
                                // Notify a client, who are in waiting state for our doMove
                                gameThread.notifyWaitState();
                                continue; // Goes to line 106 -- while (!gameThread.isGameOver()) --
                            }
                            while (true) {
                                message = in_socket.readLine();

                                // If client was disconnected
                                if (message == null) {
                                    // Close the socket if the message is null
                                    socket.close();
                                    System.out.println("Disconnected from clientt. Noo");
                                    if (name != null) {
                                        // Remove the disconnected username from the server's list
                                        serverMain.usernames.remove(name);
                                    }
                                    // Set 'BothPlayerAlive' object to false
                                    gameThread.getGame().setBothPlayerAlive(false);
                                    // Notify another player in the waiting state
                                    gameThread.notifyWaitState();
                                    break;
                                } else if (checkMoveMessage(message, out_socket)) {
                                    gameThread.getGame().resetTurnsWithoutMove();
                                    break;
                                }
                            }
                        } else {
                            // Because it's not player turn, (s)he goes to waiting state
                            gameThread.waitingState(name, out_socket);
                        }
                    }
                    // If the reason wasn't "DISCONNECT", we check the other two remaining options (DRAW, VICTORY)
                    if (gameThread.getGame().getBothPlayerAlive()) {
                        AbstractPlayer winner = (AbstractPlayer) gameThread.getGame().getWinner();
                        if (gameThread.getGame().getWinner() != null) {
                            out_socket.println(Protocol.gameOverFromServer("VICTORY", winner.getName()));
                        } else {
                            // Otherwise match is draw
                            out_socket.println(Protocol.gameOverFromServer("DRAW", null));
                        }
                    }
                } else {
                    out_socket.println("ERROR");
                }
        }


    } catch (Exception e) {
            e.printStackTrace();
        } finally {
            try {
                // Close the socket
                socket.close();
                System.out.println("Disconnected from client.");
                if (name != null) {
                    serverMain.usernames.remove(name);
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }
}
