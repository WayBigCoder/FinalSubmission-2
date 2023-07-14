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

/**
 * This class represents a client for the Othello game.
 * It implements the OthelloClient interface and
 * provides methods to connect to a server, send commands, and handle server responses.
 */
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
     * Connects the client to a specific port of the server.
     * Initializes BufferedReader and BufferedWriter based on the created socket.
     *
     * @param address the IP address of the server
     * @param port    the port to connect to
     * @return true if the connection is successful, false otherwise
     * @throws IOException if an I/O error occurs while connecting
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
     *
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
            System.out.println("[CLIENT] ERROR");
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
            // Prompt the user to enter the username
            this.clientTUI.out.print("Enter the username: ");
            this.clientTUI.out.flush();

            // Read the username from the input stream
            this.username = this.clientTUI.in.readLine();

            // Check if the username is empty
            while (this.username.trim().length() == 0) {
                this.clientTUI.out.print("Name can't be left empty! Enter the username: ");
                this.clientTUI.out.flush();

                // Read the username from the input stream
                this.username = this.clientTUI.in.readLine();
            }

            // Write the LOGIN Protocol message to the socket output stream
            out.write(Protocol.loginFromClient(this.username));
            out.newLine();
            out.flush();

        } catch (Exception e) {
            System.out.println("[CLIENT] Exception raised in handling LOGIN!");
            // Close the client connection
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

        // Flush the output stream to ensure the menu is displayed immediately
        this.clientTUI.out.flush();

        int choice;

        // Keep asking for the user's choice until a valid integer is entered
        while (true) {
            try {
                // Read the user's choice from the input stream
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

        // Perform the corresponding action based on the user's choice
        switch (choice) {
            // Send LIST command to the server
            case 1 -> sendListCommand();
            // Send QUEUE command to the server
            case 2 -> sendQueueCommand();
            // Handle the login process
            case 3 -> handleLogin();
            case 4 -> close();
            default -> {
                System.out.println("No process with this choice! Please choose again");
                handleLogin();
            }
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
        this.clientTUI.out.print("List of active players: ");
        for (int i = 1; i < parse.length; i++) {
            this.clientTUI.out.print(parse[i] + " , ");
        }
        this.clientTUI.out.println();
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
     * This method handles the situation when the client receives the NEWGAME protocol from the server.
     * It initiates the start of the game by handling the first move for both players.
     * One player places the mark, while the other player waits.
     * Then, it sends a MOVE command to the server, receives a MOVE back, and continues the game using that MOVE for the other player.
     *
     * @param input the NEWGAME protocol sent by the server
     * @throws IOException if an I/O error occurs while communicating with the server
     */
    //@ requires input != null;
    public synchronized void handleNewGame(String input) throws IOException {
        Mapping mapping = new Mapping(); // create a new mapping object to convert

        // Split the NEWGAME protocol message
        String[] parse = input.split("~");
        String name1 = parse[1];
        String name2 = parse[2];

        // Check if the first turn belongs to us
        boolean playFirst = (name1.equals(this.username)); // check if i'm indeed the 1st player

        String answer1;
        String answer2;

        // Choose AI or not?
        System.out.print("Do you want AI to play for you? (yes/no): ");
        answer1 = this.clientTUI.in.readLine();

        // Validate the answer
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

            // Create a corresponding player based on the user's answer
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
        } else { // No AI
            if (playFirst) {
                this.player = new HumanPlayer(this.username, Mark.XX);
            } else {
                this.player = new HumanPlayer(this.username, Mark.OO);
            }
        }

        System.out.println("Player " + name1 + " goes first");
        AbstractPlayer otherPlayer;

        // Create a game object between the two players
        if (playFirst) {
            otherPlayer = new HumanPlayer(name2, Mark.OO);
            game = new OthelloGame(this.player, otherPlayer);
        } else {
            otherPlayer = new HumanPlayer(name1, Mark.XX);
            game = new OthelloGame(otherPlayer, this.player);
        }

        // Print the current state of the board
        System.out.println(game.getBoard());

        // If it's our turn
        if (game.getTurn() == this.player) {
            // Find a move and send it
            Move currentMove = this.player.determineMove(this.game);
            int row = ((OthelloMove) currentMove).getRow();
            int col = ((OthelloMove) currentMove).getCol();
            int actualIndex = mapping.fromCoordinateToInt(row, col);
            sendMoveCommand(actualIndex);
        } else {
            // Waiting for the other player's turn
            System.out.println("Waiting for the other's turn!");
        }
    }

    /**
     * Handles the MOVE commands sent by the server to the client.
     *
     * @param input the MOVE protocol sent by the server
     */
    //@ requires input != null;
    public synchronized void handleMove(String input) {
        Mapping mapping = new Mapping();

        // Split the input to extract the index
        String[] parse = input.split("~"); // MOVE~index
        int index = Integer.parseInt(parse[1]);

        {
            // Convert the index to row and column
            List<Integer> result = mapping.fromIntToCoordinate(index);

            int rowConvert = result.get(0); // Extract the converted row
            int colConvert = result.get(1); // Extract the converted col

            Mark currentMark;
            if (this.game.getTurnIndex() == 0) {
                currentMark = Mark.XX;
            } else {
                currentMark = Mark.OO;
            }
            Move moveToPlaceInCell = new OthelloMove(rowConvert, colConvert, currentMark);

            // Check if the move is valid
            if (game.isValidMove(moveToPlaceInCell)) {
                this.game.doMove(moveToPlaceInCell);
                System.out.println(this.game.getBoard());

                // If the game is over
                if (this.game.isGameover()) {
                    System.out.println("Game Over");
                    return;
                }
            } else {
                System.out.println(this.player.getName() + " passed!");
                // Change the turn index to the next player
                this.game.turnIndexChange();
                // Print the updated game board
                System.out.println(this.game.getBoard());
            }
        }

        // Check if it's the player's turn and there are valid moves
        if (game.getTurn() == this.player && game.getValidMoves().size() != 0) {
            System.out.println("Your turn");

            // Determine the move for the player
            Move currentMove = this.player.determineMove(this.game);

            if (currentMove == null) {
                System.out.println("No more valid moves.");
                sendMoveCommand(64);
            } else {
                // Determine the move and send the move command
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
     * @param message which is the GAMEOVER protocol sent by the server
     */
    //@ requires message != null;
    public synchronized void handleGameOver(String message) {
        // Split the message by "~" to extract components
        String[] parse = message.split("~");
        String reason;
        String winner;

        // If the length is 2 (GAMEOVER~DRAW) it's a draw case
        if (parse.length == 2) {
            this.clientTUI.out.println("The game ended in draw"); // do we need a queue in a client to
                                                            // to keep track of the clients
        } else {
            reason = parse[1]; // Extract the reason from the parsed message
            winner = parse[2]; // Extract the winner from the parsed message
            if (reason.equals("DISCONNECT")) {
                this.clientTUI.out.println("The winner is: " + username + " - Reason of winning: " + reason);
            } else {
                this.clientTUI.out.println("The winner is: " + winner + " - Reason of winning: " + reason);
            }
        }

        // Flush the output stream
        this.clientTUI.out.flush();

        // Print the menu for the player to choose again
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

    /**
     * The main entry point of the Client application.
     * Prompts the user for an IP address and port number,
     * establishes a connection to the server, and starts a new thread for the client.
     *
     * @param args the command-line arguments
     * @throws IOException if an I/O error occurs while connecting to the server
     */
    public static void main(String[] args) throws IOException {
        Scanner sc = new Scanner(System.in);
        Client client = new Client();

        // Prompt user for IP address and port number and establish connection
        while (true) {
            try {
                System.out.print("Enter IP Address: ");
                String ip = sc.nextLine();

                System.out.print("Enter port number: ");
                String port = sc.nextLine();

                InetAddress ipAddress = InetAddress.getByName(ip);

                // Make connection
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

        // Start a new thread for the client
        new Thread(client).start();
    }
}
