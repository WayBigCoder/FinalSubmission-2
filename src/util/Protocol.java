package util;

import java.util.ArrayList;

/**
 * The Protocol class provides constants and methods for creating protocol messages.
 */
public final class Protocol {
    private Protocol() {}

    public static final String HELLO = "HELLO";
    public static final String DESCRIPTION_CLIENT = "This is client";
    public static final String LOGIN = "LOGIN";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String LIST = "LIST";
    public static final String ERROR = "ERROR";
    public static final String QUEUE = "QUEUE";
    public static final String NEWGAME = "NEWGAME";
    public static final String MOVE = "MOVE";
    public static final String GAMEOVER = "GAMEOVER";
    public static final String SEPARATOR = "~";
    public static final String DISCONNECT = "DISCONNECT";
    public static final String VICTORY = "VICTORY";
    public static final String DRAW = "DRAW";

    /**
     * Builds a new protocol message to initiate communication with the server.
     *
     * @return the protocol message
     */
    public static String helloFromClient() {
        return HELLO + SEPARATOR + DESCRIPTION_CLIENT;
    }

    /**
     * Builds a new protocol message to send the client's login information to the server.
     *
     * @param username the client's username
     * @return the protocol message
     */
    public static String loginFromClient(String username) {
        return LOGIN + SEPARATOR + username;
    }

    /**
     * Builds a new protocol message to indicate a move command.
     *
     * @return the protocol message
     */
    public static String move() {
        return MOVE;
    }

    /**
     * Builds a new protocol message to indicate an error.
     *
     * @param description the error description
     * @return the protocol message
     */
    public static String error(String description) {
        return ERROR + SEPARATOR + description;
    }

    /**
     * Builds a new protocol message to greet the client from the server.
     *
     * @param description the server description
     * @return the protocol message
     */
    public static String helloFromServer(String description) {
        return HELLO + SEPARATOR + "Server by " + description;
    }

    /**
     * Builds a new protocol message to indicate a login message from the server.
     *
     * @return the protocol message
     */
    public static String loginFromServer() {
        return LOGIN;
    }

    /**
     * Builds a new protocol message to indicate that the client is already logged in.
     *
     * @return the protocol message
     */
    public static String alreadyLoggedInFromServer() {
        return ALREADYLOGGEDIN;
    }

    /**
     * Builds a new protocol message to send the list of usernames from the server.
     *
     * @param usernames the list of usernames
     * @return the protocol message
     */
    public static String listFromServer(ArrayList<String> usernames) {
        String message = LIST;
        for (String username: usernames){
            message += (SEPARATOR + username);
        }
        return message;
    }

    /**
     * Builds a new protocol message to indicate a new game from the server.
     *
     * @param player1 the name of player 1
     * @param player2 the name of player 2
     * @return the protocol message
     */
    public static String newGameFromServer(String player1, String player2){
        return NEWGAME + SEPARATOR + player1 + SEPARATOR + player2;
    }

    /**
     * Builds a new protocol message to indicate a move from the client.
     *
     * @param index the move index
     * @return the protocol message
     */
    public static String moveFromClient(int index){
        return MOVE + SEPARATOR + index;
    }

    /**
     * Builds a new protocol message to indicate a game over situation from the server.
     *
     * @param reason the reason for game over (victory, draw or disconnect)
     * @param name   the name of winner
     * @return the protocol message
     */
    public static String gameOverFromServer(String reason, String name){
        if (reason.toUpperCase().equals(VICTORY))
            return GAMEOVER + SEPARATOR + VICTORY + SEPARATOR + name;
        if (reason.toUpperCase().equals(DRAW))
            return GAMEOVER + SEPARATOR + DRAW;
        else{
            return GAMEOVER + SEPARATOR + DISCONNECT + SEPARATOR + name;
        }
    }
}
