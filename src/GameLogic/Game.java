package GameLogic;

import java.util.List;

/**
 * A simple turn-based game.
 */
public interface Game {

    //@ pure;
    Board getBoard();

    /**
     * change the current board to the given Board in parameter.
     *
     * @param board which replaces the current board
     */
    void changeBoard(Board board);
    /**
     * Check if the game is over, i.e., there is no spaces in th board
     * or count reaches 2, meaning no moves available for 2 players, even if the board is full.
     *
     * @return whether the game is over
     */
    //@ pure;
    boolean isGameover();

    /**
     * Query whose turn it is.
     * @return the player whose turn it is
     */
    //@ ensures !isGameover() ==> getTurn() != null;
    //@ pure;
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     * @return the winner, or null if no player is the winner
     */
    //@ ensures !isGameover() ==> getWinner() == null;
    //@ pure;
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game.
     * @return the list of currently valid moves
     */
    //@ ensures (\forall Move m; \result.contains(m); isValidMove(m));
    //@ ensures !isGameover() ==> getValidMoves().size() > 0;
    //@ pure;
    List<Move> getValidMoves();

    /**
     * Check if a move is a valid move.
     * @param move the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
    //@ pure;
    boolean isValidMove(Move move);

    /**
     * Perform the move, assuming it is a valid move.
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);
}
