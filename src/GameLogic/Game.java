package GameLogic;

import java.util.List;

/**
 * The interface for a game.
 */
public interface Game {

    //@ pure;
    Board getBoard();

    /**
     * change the current board to the given Board in parameter.
     *
     * @param boardCopy which replaces the current board
     */
    void changeBoard(Board boardCopy);

    /**
     * Check if the game is over.
     * Condition:
     * 1) there is no spaces in th board
     * or 2) count reaches 2, meaning no moves available for 2 players, even if the board is not full.
     *
     * @return true if the game is over, false otherwise
     */
    //@ pure;
    boolean isGameover();

    /**
     * Query whose turn it is.
     *
     * @return the player whose turn it is
     */
    //@ ensures !isGameover() ==> getTurn() != null;
    //@ pure;
    Player getTurn();

    /**
     * Gets the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the winner, or null if no player is the winner
     */
    //@ ensures !isGameover() ==> getWinner() == null;
    //@ pure;
    Player getWinner();

    /**
     * Returns a list of all moves that are valid in the current state of the game.
     *
     * @return the list of currently valid moves
     */
    //@ ensures (\forall Move m; \result.contains(m); isValidMove(m));
    //@ ensures !isGameover() ==> getValidMoves().size() > 0;
    //@ pure;
    List<Move> getValidMoves();

    /**
     * Checks if a move is valid.
     *
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    //@ ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
    //@ pure;
    boolean isValidMove(Move move);

    /**
     * Performs the given move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);
}
