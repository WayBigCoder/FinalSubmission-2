package Networking;

import GameLogic.*;

import java.io.PrintWriter;
import util.Protocol;
/**
 * A class created for 2 Threads, playing the same game and sharing common objects.
 */
public class GameThread {

    private final ServerThread server_thread1;
    private final AbstractPlayer player1;
    private final ServerThread server_thread2;
    private final AbstractPlayer player2;
    private final Game game;
    // Flag indicating if a move has been completed by a player in the game.
    private boolean moveIsDone = false;
    // The index of the move made by a player in the game.
    public int moveIndex;
    private final Object lock = new Object();

    // Constructor
    /**
     * Creates a GameThread object with two server threads of both clients.
     *
     * @param server_thread1 Server of 1st client
     * @param server_thread2 Server of 2nd client
     */
    public GameThread(ServerThread server_thread1, ServerThread server_thread2) {
        this.server_thread1 = server_thread1;
        this.server_thread2 = server_thread2;
        player1 = new HumanPlayer(this.server_thread1.getName(), Mark.XX);
        player2 = new HumanPlayer(this.server_thread2.getName(), Mark.OO);
        game = new OthelloGame(player1, player2);
    }

    /**
     * Returns the name of the first player.
     *
     * @return Name of player 1
     */
    public String name1() {
        return this.server_thread1.getName();
    }

    /**
     * Returns the name of the second player.
     *
     * @return Name of player 2
     */
    public String name2() {
        return this.server_thread2.getName();
    }

    /**
     * Returns the OthelloGame object.
     *
     * @return OthelloGame object
     */
    public OthelloGame getGame() {
        return (OthelloGame) this.game;
    }

    /**
     * Sets the value for the moveIsDone flag.
     *
     * @param state New state for the moveIsDone flag
     */
    public void setMoveIsDone(boolean state) {
        moveIsDone = state;
    }

    /**
     * Checks if the game is over.
     *
     * @return True if the game is over, false otherwise
     */
    public boolean isGameOver() {
        return this.game.isGameover();
    }

    /**
     * Returns the name of the player whose turn it is.
     *
     * @return Name of the player
     */
    public String nameForTurn() {
        if (this.game.getTurn() == player1) {
            return player1.getName();
        } else {
            return player2.getName();
        }
    }

    /**
     * This method will notify the waiting Thread, that move is done, and it could be woken up.
     */
    public void notifyWaitState() {
        synchronized (lock) {
            while (!moveIsDone) {
                setMoveIsDone(true);
            }
            lock.notifyAll();
        }
    }

    /**
     * Do move for the Thread whose turn it is.
     * ---
     * Before Thread is calling this method,
     * it has already extracted the INDEX from client message and assign it to moveIndex object
     */
    public void makeMove() {
        HumanPlayer currentPlayer = (HumanPlayer) this.game.getTurn();

        Move currentMove = new OthelloMove(this.game.getBoard().row(moveIndex), this.game.getBoard().col(moveIndex), currentPlayer.getMark());
        // If chosen move is valid
        if (this.game.isValidMove(currentMove)) {
            this.game.doMove(currentMove);
        }
        //Notify second Thread that Move is done
        notifyWaitState();
    }

    /**
     * Implements a waiting state for a given thread.
     * This method is called for the thread whose turn has not yet come.
     * The thread goes into a wait state if another thread has not made a move yet.
     * After another thread finishes its move, it will notify the waiting thread.
     *
     * @param name        The name of the thread
     * @param out_socket  The PrintWriter object to which data is written
     * @throws InterruptedException Thrown when a waiting thread is interrupted
     */
    public synchronized void waitingState(String name, PrintWriter out_socket) throws InterruptedException {
        synchronized (lock) {
            if (!moveIsDone) {
                try {
                    // Put the thread in a waiting state until notified
                    lock.wait();
                } catch (InterruptedException e) {
                    // Handle the exception
                }
            }
            // If both players still online, then the player, who was in wait state, will do move
            // Otherwise, the server will send the "DISCONNECT" message
            if (this.getGame().areBothPlayersAlive()) {
                // Reset the moveIsDone flag for the next turn
                setMoveIsDone(false);
                // Send a move, which was done by another player, to the player, who was waiting
                out_socket.println(Protocol.moveFromClient(moveIndex));
            } else {
                out_socket.println(Protocol.gameOverFromServer("DISCONNECT", nameForTurn()));
            }
        }
    }
}
