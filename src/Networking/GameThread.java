package Networking;

import GameLogic.*;

import java.io.PrintWriter;
import util.Protocol;
/**
 * A class created for 2 Threads, playing the same game and sharing common objects
 */
public class GameThread {

    private final ServerThread server_thread1;
    private final AbstractPlayer player1;
    private final ServerThread server_thread2;
    private final AbstractPlayer player2;

    private final Game game;
    //moveIsDone helps to keep one of the Thread in wait state, while another thread doesn't make move yet
    private boolean moveIsDone = false;
    //this object keeps the index of Move, as soon as one of the clients send the valid move
    public int moveIndex;
    private final Object lock = new Object();

    //constructor
    public GameThread(ServerThread server_thread1, ServerThread server_thread2) {
        this.server_thread1 = server_thread1;
        this.server_thread2 = server_thread2;
        player1 = new HumanPlayer(this.server_thread1.getName(), Mark.XX);
        player2 = new HumanPlayer(this.server_thread2.getName(), Mark.OO);
        game = new OthelloGame(player1, player2);
    }
    /**
     * Give name for first thread
     * @return name of player 1
     */
    public String name1(){
        return this.server_thread1.getName();
    }
    /**
     * Give name for second thread
     * @return name of player 2
     */
    public String name2(){
        return this.server_thread2.getName();
    }

    /**
     * Getter for Game object
     * @return OthelloGame object
     */
    public OthelloGame getGame(){
        return (OthelloGame) this.game;
    }

    /**
     * Set the value for moveIsDone object
     */
    public void setMoveIsDone(boolean state){
        moveIsDone = state;
    }
    /**
     * Checks if the game is over
     * @return boolean value
     */
    public boolean isGameOver(){
        return this.game.isGameover();
    }

    /**
     * Returns the name of the player whose turn it is.
     * @return name of the player
     */
    public String nameForTurn(){
        if (this.game.getTurn() == player1){
            return player1.getName();
        }else{
            return player2.getName();
        }
    }

    /**
     * This method will notify the waiting Thread, that move is done, and it could be woken up
     */
    public void notifyWaitState(){
        synchronized (lock) {
            while(!moveIsDone){
                setMoveIsDone(true);
            }
            lock.notifyAll();
        }
    }

    /**
     * Do move for the Thread whose turn it is
     * ---
     * Before Thread is calling this method,
     * it has already extracted the INDEX from client message and assign it to moveIndex object
     */
    public void makeMove(){
        HumanPlayer currentPlayer = (HumanPlayer) this.game.getTurn();

        Move currentMove = new OthelloMove(this.game.getBoard().row(moveIndex), this.game.getBoard().col(moveIndex), currentPlayer.getMark());
        if (this.game.isValidMove(currentMove)){
            this.game.doMove(currentMove);
        }
        //Notify second Thread that Move is done
        notifyWaitState();
    }

    /**
     * A synchronized method that implements a waiting state for a given thread.
     * -------
     * This method is called for the Thread, whose turn has NOT yet come.
     * This Thread goes to the wait state , if another Thread has not made move yet.
     * After another Thread finish its move, it will notify the Thread in the waiting state
     *
     * @param name - The name of the thread
     * @param out_socket - The PrintWriter object to which data is written
     * @throws InterruptedException - Thrown when a waiting thread is interrupted
     */
    public synchronized void waitingState(String name, PrintWriter out_socket) throws InterruptedException {
        synchronized (lock) {
            if (!moveIsDone) {
                try {
                    lock.wait();
                } catch (InterruptedException e) {
                    // Handle the exception
                }
            }
            //if both players still online,then the player, who was in wait state, will do move
            //otherwise the Protocol msg "DISCONNECT" will be sent from Server
            if (this.getGame().getBothPlayerAlive()){
                //Since Thread was waking up, we can back MoveIsDone to false.
                setMoveIsDone(false);
                //send a move, which was done by another Thread, to the Thread, who was waiting
                out_socket.println(Protocol.moveFromClient(moveIndex));
            } else {
                out_socket.println(Protocol.gameOverFromServer("DISCONNECT", nameForTurn() ));
            }
        }
    }
}
