package util;

import java.util.ArrayList;

/**
 * networking.Util.Protocol class with constants and methods for creating protocol messages
 */
public final class Protocol {
    private Protocol() {}

    public static final String HELLO = "HELLO";
    public static final String DESCRIPTION_CLIENT = "This is client";
    public static final String DESCRIPTION_SERVER = "This is server";
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
     * Build a new protocol description which instructs the networking.server that you want to say something
     * @return the protocol message
     */
    //for
    public static String helloFromClient() {
        return HELLO + SEPARATOR + DESCRIPTION_CLIENT;
    }
    public static String helloFromServer() {
        return HELLO + SEPARATOR + DESCRIPTION_SERVER;
    }
    public static String loginFromClient(String username) {
        return LOGIN + SEPARATOR + username;
    }
    public static String loginFromServer(String username) {
        return LOGIN;
    }
    public static String alreadyLoggedInFromServer(String username) {
        return ALREADYLOGGEDIN;
    }
    public static String requestListFromClient() {
        return LIST;
    }
    public static String queueFromClient() {
        return QUEUE;
    }
    public static String newGame() {
        return NEWGAME;
    }
    public static String move() {
        return MOVE;
    }
    public static String error(String description) {
        return ERROR + SEPARATOR + description;
    }
    public static String GAMEOVER(String message) {
        return GAMEOVER;
    }

    public static String helloFromClient(String description) {
        return HELLO + SEPARATOR + "Client by " + description;
    }

    public static String helloFromServer(String description) {
        return HELLO + SEPARATOR + "Server by " + description;
    }

    public static String loginFromServer() {
        return LOGIN;
    }

    public static String alreadyLoggedInFromServer() {
        return ALREADYLOGGEDIN;
    }
    public static String listFromServer(ArrayList<String> usernames) {
        String message = LIST;
        for (String username: usernames){
            message += (SEPARATOR + username);
        }
        return message;
    }
    public static String newGameFromServer(String player1, String player2){
        return NEWGAME + SEPARATOR + player1 + SEPARATOR + player2;
    }
    public static String moveFromClient(int index){
        return MOVE + SEPARATOR + index;
    }
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
