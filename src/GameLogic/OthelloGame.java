package GameLogic;


import java.util.ArrayList;
import java.util.List;

/**
 * The Othello game class, consisting of all the necessary game mechanics.
 */
public class OthelloGame implements Game {
    private Board board;
    private AbstractPlayer player1;
    private AbstractPlayer player2;
    private int turnIndex;  // O for black, 1 for white
    private int turnsWithoutMoveCount;      // If count reaches 2, then both players don't have moves, even if the board are not full
    private boolean areBothPlayersAlive; // True = both players alive, false = at least one player disconnected

    /**
     * Creates an OthelloGame with the assigned two players.
     *
     * @param player1 the first player
     * @param player2 the second player
     */
    public OthelloGame(AbstractPlayer player1, AbstractPlayer player2) {
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        this.turnIndex = 0;
        this.turnsWithoutMoveCount = 0;
        this.areBothPlayersAlive = true;
    }

    /**
     * Gets the board of the game.
     *
     * @return the game board
     */
    public Board getBoard() {
        return this.board;
    }

    /**
     * Changes the current board to the given board copy.
     *
     * @param boardCopy the board that replaces the current board
     */
    public void changeBoard(Board boardCopy){
        this.board = boardCopy;
    }

    /**
     * Increments the count of turns without a move for the current player.
     */
    public void incrementTurnsWithoutMove() {
        this.turnsWithoutMoveCount += 1;
    }

    /**
     * Returns the count of turns without a move for the current player.
     *
     * @return the count of turns without a move
     */
    public int getTurnsWithoutMove() {
        return this.turnsWithoutMoveCount;
    }

    /**
     * Resets the count of turns without a move to zero when at least one player has a move.
     */
    public void resetTurnsWithoutMove() {
        this.turnsWithoutMoveCount = 0;
    }
    @Override
    public boolean isGameover() {
        return turnsWithoutMoveCount == 2 || board.isFull() || !areBothPlayersAlive;
    }

    /**
     * Sets the status of both players (alive (true) or disconnected (false)).
     *
     * @param status the status of both players
     */
    public void setAreBothPlayersAlive(boolean status){
        this.areBothPlayersAlive = status;
    }

    /**
     * Returns the status of both players.
     *
     * @return true if both players are alive, false otherwise
     */
    public boolean areBothPlayersAlive(){
        return this.areBothPlayersAlive;
    }

    @Override
    public Player getTurn() {
        if (turnIndex == 0)
            return player1;
        else
            return player2;
    }

    /**
     * Changes the turn index between 0 and 1.
     */
    //@ ensures \old(turnIndex) == 0 ==> turnIndex == 1;
    //@ ensures \old(turnIndex) == 1 ==> turnIndex == 0;
    public void turnIndexChange(){
        // O for black, 1 for white
        turnIndex = turnIndex == 0 ? 1 : 0;
    }

    /**
     * Gets the current turn index.
     *
     * @return the current turn index (0 or 1)
     */
    public int getTurnIndex(){
        return turnIndex;
    }

    @Override
    public Player getWinner() {
        if (board.getWinnerMark() == Mark.XX)
            return player1;
        else if ((board.getWinnerMark() == Mark.OO))
            return player2;
        // If draw, null will be returned
        return null;
    }

    @Override
    public List<Move> getValidMoves() {
        // List to store the valid moves
        List<Move> moves = new ArrayList<>();
        Mark currentMark = turnIndex == 0 ? Mark.XX : Mark.OO;

        // Iterate over the rows of the board
        for (int i = 0; i < board.DIM; i++)
            // Iterate over the columns of the board
            for (int j = 0; j < board.DIM; j++)
            {
                // Create a move object for the current position
                Move currentMove = new OthelloMove(i, j, currentMark);

                if (isValidMove(currentMove))
                    moves.add(currentMove); // Add the valid move to the list of moves
            }
        return moves;
    }


    @Override
    public boolean isValidMove(Move move) {
        if (!(move instanceof OthelloMove)) {
            return false;
        }
        OthelloMove omove = (OthelloMove) move;

        //check is Field Empty and Valid
        return (board.isEmptyField(omove.getRow(), omove.getCol()) &&
                board.checkMove(omove.getRow(), omove.getCol(), omove.getMark()));
    }

    @Override
    public void doMove(Move move) {
        OthelloMove tttm = (OthelloMove) move;
        this.board.setField(tttm.getRow(), tttm.getCol(), tttm.getMark());

        /*
        * If doMove was called, the move is valid, and at least one opponent's disc should be flipped,
        * as the indexes of the discs that should be flipped are stored in board.flippedDiscs array.
        * Iterate through each index in flippedDiscs and set the corresponding field on the board to the mark of the move.
         */
        for (int i = 0; i<this.board.flippedDiscs.size() ; i ++){
            this.board.setField(board.row(board.flippedDiscs.get(i)), board.col(board.flippedDiscs.get(i)), tttm.getMark());
        }

        // Change index of player after valid move is done
        turnIndexChange();
    }
}

