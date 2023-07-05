package Networking;

import GameLogic.AbstractPlayer;
import java.io.*;
import java.net.Socket;
import util.Protocol;

/**
 * All of this code is run for every new client individually
 */
public class ServerThread implements Runnable {
    private Socket socket;
    private ServerMain serverMain;
    private GameThread gameThread;
    private String name;

    //constructor
    public ServerThread(Socket socket, ServerMain serverMain){
        this.socket = socket;
        this.serverMain = serverMain;
    }
    //getter
    public String getName() {
        return name;
    }



    /**
     * Checks whether the Client ,which turn it is, sends the MOVE message.
     * (only MOVE~INDEX message is accepted, when it comes to your turn)
     *
     * @param message of ServerThread who's turn it is
     * @param out_socket outgoing for sending messages to client
     * @return boolean
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

            //incoming
            BufferedReader in_socket = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            //outgoing
            PrintWriter out_socket = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true);

            String message;

            //HANDSHAKE
            while (true) {
                //read message from client side
                message = in_socket.readLine();
                if (message == null) {
                    System.out.println("Client has disconnected.");
                    socket.close(); // close the socket
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

            //MAIN COMMANDS
            while (true) {
                message = in_socket.readLine();

                if (message == null) {
                    socket.close(); // close the socket
                    System.out.println("Disconnected from client.");
                    if (name != null) {
                        serverMain.usernames.remove(name);
                    }
                    break;

                }else if (message.startsWith("LIST")){
                    out_socket.println(Protocol.listFromServer(serverMain.usernames));

                }else if (message.startsWith("QUEUE")){
                    //as soon this command is called, the game loop is started
                    //in below line the code can be paused, as Thread can be in wait() state in AddToQueue method
                    gameThread = serverMain.addToQueue(this);
                    //send Protocol msg to Clients about new game
                    out_socket.println(Protocol.newGameFromServer(gameThread.name1(),gameThread.name2()));

                    while (!gameThread.isGameOver()){
                        //if player's name, which turn it is, matches with thread's name object
                        //then it is expecting only MOVE command from client , otherwise error
                        if (gameThread.nameForTurn().equals(name)){

                            //if client, whose turn it is, doesn't have valid moves
                            if(gameThread.getGame().getValidMoves().size() == 0) {
                                gameThread.getGame().turnIndexChange();
                                //if count reaches two, means two players don't have valid moves
                                gameThread.getGame().incrementTurnsWithoutMove();
                                out_socket.println(Protocol.moveFromClient(64));
                                gameThread.moveIndex = 64;
                                //notify a client, who are in waiting state for our doMove
                                gameThread.notifyWaitState();
                                continue; //goes to line 106 -- while (!gameThread.isGameOver()) --
                            }
                            while (true){
                                message = in_socket.readLine();
                                if(message == null){
                                    break;
                                }

                                if (checkMoveMessage(message, out_socket)) {
                                    gameThread.getGame().resetTurnsWithoutMove();
                                    break;
                                }
                            }
                        }else{
                            gameThread.waitingState(name, out_socket);
                        }
                    }
                    AbstractPlayer winner = (AbstractPlayer) gameThread.getGame().getWinner();
                    if (gameThread.getGame().getWinner() != null)
                        out_socket.println(Protocol.gameOverFromServer("VICTORY", winner.getName()));
                    else{//match is draw
                        out_socket.println(Protocol.gameOverFromServer("DRAW", null));}
                }else{
                    out_socket.println("ERROR");
                }
        }


    } catch (Exception e) {
            e.printStackTrace();
        } finally {
            try {
                socket.close(); // close the socket
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
