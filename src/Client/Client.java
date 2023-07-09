package Client;

import ArtificialIntelligence.ComputerPlayer;
import ArtificialIntelligence.NaiveStrategy;
import ArtificialIntelligence.SmartStrategy;
import GameLogic.*;
import util.Mapping;
import util.Protocol;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.List;
import java.util.Scanner;

public class Client implements OthelloClient, Runnable {
    Socket socket;
    private BufferedReader in;
    private BufferedWriter out;
    private ClientTUI clientTUI;

    private String username;
    private AbstractPlayer player;
    private OthelloGame game;

    /**
     * Constructor when first created that initializes:
     * socket to be null for later creation
     * a new TUI object to receive System.in and print System.out.
     */
    public Client() {
        this.socket = null;
        this.clientTUI = new ClientTUI();
    }

    /**
     * This boolean method should return true on success or false on failure,
     * in terms of a client connecting to a specific port of server
     *
     * In case an exception is thrown, then print out the message
     * indicating the error, then close the socket and return false
     *
     * Finally, this method will initialize BufferedReader and BufferedWriter
     * based on the recent created socket
     *
     * @param address, which is the IP address of the server
     * @param port, which is the port that you want to connect to
     * @return true if successfully connected; else false
     * @throws IOException
     */
    //@ ensures \result == true || \result == false;
    @Override
    public boolean connect(InetAddress address, int port) throws IOException {
        try {
            this.socket = new Socket(address, port);
            System.out.println("[CLIENT] Connect to " + address);
            return true;
        } catch (IOException e) {
            System.out.println("[CLIENT] Cannot connect");
            return false;
        } finally {
            out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        }

    }


    /**
     * Get the username of the player.
     * @return player's username
     */
    //@ ensures \result == this.username;
    public String getUsername() {
        return this.username;
    }


    /**
     * Disconnect from server by closing the socket as well as the buffered writer.
     */
    //@ ensures this.socket.isClosed()==true;
    @Override
    public void close() {
        try {
            this.socket.close();
            this.out.close();
        } catch (Exception e) {
            System.out.println("[CLIENT] Cannot close the socket/out");
        }
    }

    /**
     * Send HELLO command from the client to server.
     *
     * In case an exception is thrown, then print out the message
     * indicating the error, then close the socket
     */
    public synchronized void sendHelloCommand() {
        try {
            out.write(Protocol.helloFromClient());
            out.newLine();
            out.flush();
        } catch (Exception e) {
            System.out.println("[CLIENT] Exception raised in sending hello");
            close();
        }

    }


    /**
     * This method shows how to process if Client receives back HELLO protocol from server.
     * In case an exception is thrown, then print out the message
     * indicating the error
     */
    public synchronized void handleHello() {
        try {
            this.clientTUI.out.print("Enter the username: "); // print to console
            this.clientTUI.out.flush();

            this.username = this.clientTUI.in.readLine(); // take the username

            while (this.username.trim().length() == 0) {
                this.clientTUI.out.print("Name can't be left empty! Enter the username: ");
                this.clientTUI.out.flush();

                this.username = this.clientTUI.in.readLine();
            }

            out.write(Protocol.loginFromClient(this.username)); // write the message including username to socket
            out.newLine();
            out.flush();

        } catch (Exception e) {
            System.out.println("[CLIENT] Exception raised in handling LOGIN!");
            this.close();
        }
    }

    /**
     * This method is to print out the menu with options to be chosen
     * Option 1: Send the LIST protocol to the server -> to receive a list of act
     * Option 2: Send the QUEUE protocol to the server -> player gets to the queue and wait for opponent
     * Option 3: Print out the help menu that displays options to choose
     * Option 4: Quit by simply closing the socket
     */
    public synchronized void printMenu() {
        this.clientTUI.out.println("=================MENU================\n");
        this.clientTUI.out.println("\t1. LIST\n");
        this.clientTUI.out.println("\t2. QUEUE\n");
        this.clientTUI.out.println("\t3. HELP\n");
        this.clientTUI.out.println("\t4. QUIT\n");
        this.clientTUI.out.println("=====================================\n");

        this.clientTUI.out.flush();

        int choice;

        while (true) {
            try {
                System.out.print("Enter your choice: ");
                String line = this.clientTUI.in.readLine();
                choice = Integer.parseInt(line);
                break;
            } catch (NumberFormatException e) {
                System.out.println("Wrong format! Cannot convert into integer!");

            } catch (IOException e) {
                System.out.println("[CLIENT] Error when reading choices input");;
            }
        }

        switch (choice) {
            case 1:
                sendListCommand(); // send LIST command to the server
                break;
            case 2:
                sendQueueCommand(); // send QUEUE command to the server
                break;
            case 3:
                handleLogin(); // handle with logging in
                break;
            case 4:
                close();
                break;
            default:
                System.out.println("No process with this choice! Please choose again");
                handleLogin();
        }
    }


    /**
     * This method shows how to process if Client receives back LOGIN protocol from server
     * which is storing this client to a list for future using
     * and printing out the menu
     *
     */
    public synchronized void handleLogin() {
        printMenu();
    }


    /**
     * This boolean method should return true on success or false on failure,
     * in terms of sending the LIST protocol from the client to server
     *
     * In case an exception is thrown, then print out the message
     * indicating the error, then close the socket and return false
     *
     * @return true if no errors were found; else false
     */
    //@ ensures \result == true || \result == false;
    public synchronized boolean sendListCommand() {
        try {
            out.write(Protocol.LIST);
            out.newLine();
            out.flush();

            return true;
        } catch (IOException e) {
            System.out.println("[CLIENT] Exception raised in sending LIST command");
            close();
            return false;
        }
    }

    /**
     * This boolean method should return true on success or false on failure,
     * in terms of sending the protocol QUEUE to the server.
     *
     * In case an exception is thrown, then print out the message
     * indicating the error, then close the socket and return false
     *
     * @return true if QUEUE command was sent successfully; else false
     */
    //@ ensures \result == true || \result == false;
    public synchronized boolean sendQueueCommand() {
        try {
            out.write(Protocol.QUEUE);
            out.newLine();
            out.flush();

            this.clientTUI.out.println("[CLIENT] Waiting for other player...");
            this.clientTUI.out.flush();

            return true;
        } catch (IOException e) {
            System.out.println("[CLIENT] Exception raised in sending QUEUE command");
            close();
            return false;
        }
    }


    /**
     * This method is to handle when client receives LIST command from server
     * It should print out to the console a list of usernames that are
     * currently logged into the server
     *
     * @param message, which is a list name of active users
     */
    //@ requires message!=null;
    public synchronized void handleList(String message) {
        String[] parse = message.split("~");
        for (int i = 1; i < parse.length; i++) {
            this.clientTUI.out.println(parse[i]);
        }
        this.clientTUI.out.flush();

        printMenu();

    }

    /**
     * Send error to the server by indicating specific message for that error
     *
     * In case an exception is thrown, then print out the message
     * indicating the error, then close the socket and return false
     *
     * @param message, which is the error specification
     */
    //@ requires message != null;
    public synchronized void sendError(String message) {
        try {
            out.write(Protocol.error(message));
            out.newLine();
            out.flush();

        } catch (IOException e) {
            System.out.println("[CLIENT] Exception raised in sending ERROR command");
            close();
        }
    }


    /**
     * This boolean method should return true on success or false on failure,
     * in terms of sending the protocol MOVE to the server.
     *
     * In case an exception is thrown, then print out the message
     * indicating the error, then close the socket and return false
     *
     * @param index, the index that player wants to send
     * @return true if MOVE is sent successfully; else false
     */
    //@ ensures \result == true || \result == false;
    //@ requires 0 <= index && index <= 64;
    public synchronized boolean sendMoveCommand(int index) {
        String moveProtocol = Protocol.move() + Protocol.SEPARATOR + index;

        try {
            out.write(moveProtocol);
            out.newLine();
            out.flush();

            return true;
        } catch (IOException e) {
            System.out.println("[CLIENT] Exception raised in sending MOVE command");
            sendError("Sending MOVE command");
            close();
            return false;
        }
    }

    /**
     * This method handles when the client receives NEWGAME protocol from the server
     * The method starts handling the first move for both players, where one will place the Mark
     * and the other will be in waiting state. Then, it sends MOVE to the server, the server
     * sends MOVE back and client continues using that MOVE for the other player
     *
     * @param input, which is the NEWGAME protocol sent by the server
     * @throws IOException
     */
    //@ requires input != null;
    public synchronized void handleNewGame(String input) throws IOException {
        Mapping mapping = new Mapping(); // create a new mapping object to convert

        // receive NEWGAME protocol
        String[] parse = input.split("~");
        String name1 = parse[1];
        String name2 = parse[2];

        // check if the first turn belongs to us
        boolean playFirst = (name1.equals(this.username)); // check if i'm indeed the 1st player

        String answer1;
        String answer2;

        // Choose AI or not?
        System.out.print("Do you want AI to play for you? (yes/no): ");
        answer1 = this.clientTUI.in.readLine();

        while (!answer1.equals("yes") && !answer1.equals("no")) {
            System.out.print("Please enter your option again (yes/no): ");
            answer1 = this.clientTUI.in.readLine();
        }

        if (answer1.equals("yes")) {
            // Ask which AI
            System.out.print("Which AI do you want to use Naive or Smart? (-N/-S) : ");
            answer2 = this.clientTUI.in.readLine();

            while (!answer2.equals("-N") && !answer2.equals("-S")) {
                System.out.print("Please enter your option again (-N/-S): ");
                answer2 = this.clientTUI.in.readLine();
            }

            // if this is indeed our turn
            // then create a corresponding player
            if (playFirst) {
                if (answer2.equals("-N")) {
                    this.player = new ComputerPlayer(Mark.XX, new NaiveStrategy());
                } else {
                    this.player = new ComputerPlayer(Mark.XX, new SmartStrategy());
                }
            } else {
                if (answer2.equals("-N")) {
                    this.player = new ComputerPlayer(Mark.OO, new NaiveStrategy());
                } else {
                    this.player = new ComputerPlayer(Mark.OO, new SmartStrategy());
                }
            }
        } else { // answer is no
            if (playFirst) {
                this.player = new HumanPlayer(this.username, Mark.XX);
            } else {
                this.player = new HumanPlayer(this.username, Mark.OO);
            }
        }


        System.out.println("Player " + name1 + " goes first");
        AbstractPlayer otherPlayer;

        // next, create a game object between the 2 players
        if (playFirst) {
            otherPlayer = new HumanPlayer(name2, Mark.OO);
            game = new OthelloGame(this.player, otherPlayer);

        } else {
            otherPlayer = new HumanPlayer(name1, Mark.XX);
            game = new OthelloGame(otherPlayer, this.player);
        }

        // then print out the board to observe the state
        System.out.println(game.getBoard());

        // if this is our turn
        if (game.getTurn() == this.player) {

            // then, we'll find a move and send this move
            Move currentMove = this.player.determineMove(this.game);
            int row = ((OthelloMove) currentMove).getRow();
            int col = ((OthelloMove) currentMove).getCol();
            int actualIndex = mapping.fromCoordinateToInt(row, col);

            sendMoveCommand(actualIndex);

        } else { // else, we'll be waiting
            System.out.println("Waiting for the other's turn!");
        }


    }


    /**
     * This method handles MOVE commands sent by server that the client receives.
     * @param input, which is the MOVE protocol sent by the server
     */
    //@ requires input!=null;
    public synchronized void handleMove(String input) {
        Mapping mapping = new Mapping();

        // the server responses the MOVE
        String[] parse = input.split("~"); // MOVE~index
        int index = Integer.parseInt(parse[1]);

        {
            List<Integer> result = mapping.fromIntToCoordinate(index);

            int rowConvert = result.get(0);
            int colConvert = result.get(1);

            Mark currentMark;
            if (this.game.getTurnIndex() == 0) {
                currentMark = Mark.XX;
            } else {
                currentMark = Mark.OO;
            }
            Move moveToPlaceInCell = new OthelloMove(rowConvert, colConvert, currentMark);

            if (game.isValidMove(moveToPlaceInCell)) {
                this.game.doMove(moveToPlaceInCell);
                System.out.println(this.game.getBoard());
                if (this.game.isGameover()) {
                    System.out.println("Game Over");
                    return;
                }


            } else {
                System.out.println(this.player.getName() + " passed!");
                this.game.turnIndexChange();
                System.out.println(this.game.getBoard());
            }
        }

        // check if the next move is our move or not
        if (game.getTurn() == this.player && game.getValidMoves().size() != 0) {
            System.out.println("Your turn");

            Move currentMove = this.player.determineMove(this.game);

            if (currentMove == null) {

                System.out.println("No more valid moves.");

                sendMoveCommand(64);

            } else { // determine the move and send the move
                int row = ((OthelloMove) currentMove).getRow();
                int col = ((OthelloMove) currentMove).getCol();
                int actualIndex = mapping.fromCoordinateToInt(row, col);

                sendMoveCommand(actualIndex);
            }
        } else {
            System.out.println("Waiting for the other's turn!");
        }


        }


    /**
     * This method handles GAMEOVER command sent by server that the client receives
     * It prints out who the winner is and what the reason of victory, then
     * print out the menu for player to choose again
     *
     * @param message, which is the GAMEOVER protocol sent by the server
     */
    //@ requires message != null;
    public synchronized void handleGameOver(String message) {
        String[] parse = message.split("~"); // GAMEOVER~reason~name or GAMEOVER~draw
        String reason;
        String winner;

        if (parse.length == 2) { // draw case
            this.clientTUI.out.println("The game ended in draw"); // do we need a queue in a client to
                                                            // to keep track of the clients
        } else {
            reason = parse[1];
            winner = parse[2];
            if (reason.equals("DISCONNECT")){
                this.clientTUI.out.println("The winner is: " + username + " - Reason of winning: " + reason);
            } else {
                this.clientTUI.out.println("The winner is: " + winner + " - Reason of winning: " + reason);
            }
        }

        this.clientTUI.out.flush();

        printMenu();

    }


    /**
     * This method will handle the commands that the server receives from the client.
     * The client receives a string (which is the protocol sent from server) and then
     * based on the first word of protocol can the method classifies into different cases
     * @param input, which is the protocol received from the server
     * @throws Exception
     */
    //@ requires input!=null;
    public synchronized void commandHandle(String input) throws Exception {
        System.out.println(input);
        String[] parse = input.split("~");
        switch (parse[0]) {
            case Protocol.ALREADYLOGGEDIN:
                System.out.println("Please enter a new username!");
            case Protocol.HELLO:
                handleHello();
                break;
            case Protocol.LOGIN:
                handleLogin();
                break;
            case Protocol.LIST:
                handleList(input);
                break;
            case Protocol.NEWGAME:
                handleNewGame(input);
                break;
            case Protocol.MOVE:
                handleMove(input);
                break;
            case Protocol.GAMEOVER:
                handleGameOver(input);
                break;
            default:
                throw new Exception("Command is invalid");
        }

    }

    /**
     * Start thread with a client object.
     */
    @Override
    public void run() {
        sendHelloCommand();
        while (true) {
            try {
                in = new BufferedReader(new InputStreamReader(socket.getInputStream()));

                String msg = in.readLine();
                if (msg == null) {
                    this.close();
                    System.out.println("Msg is null");
                    continue;
                }
                commandHandle(msg);
            } catch (IOException e) {
                this.close();
                System.out.println("Socket is closed! Closing the program");
                break;
            } catch (Exception e) {
                System.out.println("Invalid command");
            }
        }
    }


    public static void main(String[] args) throws IOException {
        Scanner sc = new Scanner(System.in);
        Client client = new Client();

        while (true) {
            try {
                System.out.print("Enter IP Address: ");
                String ip = sc.nextLine();

                System.out.print("Enter port number: ");
                String port = sc.nextLine();

                InetAddress ipAddress = InetAddress.getByName(ip);

                // make connection
                System.out.println("Starting to connect to the client");
                if (!client.connect(ipAddress, Integer.parseInt(port))) {
                    System.out.println("Failed to connect");
                } else {
                    break;
                }

            } catch (Exception e) {
                System.out.println("[CHAT] Cannot connect the client");
                client.close();
            }
        }

        System.out.println("Client connected");

        new Thread(client).start();
    }

}
