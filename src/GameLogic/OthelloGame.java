package GameLogic;


import java.util.ArrayList;
import java.util.List;

/**
 * Game class, consisting all needed game mechanics
 */
public class OthelloGame implements Game {
    private Board board;
    private AbstractPlayer player1;
    private AbstractPlayer player2;
    private int turnIndex;  //O for black, 1 for white
    private int count;      //if count reaches 2, then both players don't have moves, even if the board are not full
    private boolean bothPlayerAlive; //true = both players alive, false = at least one player disconnected

    /**
     * Create an OthelloGame with assigned 2 players
     * @param player1
     * @param player2
     */
    public OthelloGame(AbstractPlayer player1, AbstractPlayer player2) {
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        this.turnIndex = 0;
        this.count = 0;
        this.bothPlayerAlive = true;
    }

    /**
     * Get the board
     * @return the board
     */
    public Board getBoard() {
        return this.board;
    }

    /**
     * Change this board to whichever board that is passed in parameter
     * @param boardcopy which replaces the current board
     */
    public void changeBoard(Board boardcopy){
        this.board = boardcopy;
    }

    /**
     * If the current player doesn't have move, we call this method to increase the count by 1
     * @return
     */
    public void incrementTurnsWithoutMove() {
        this.count += 1;
    }

    /**
     * Getter for count object
     * @return the value of count
     */
    public int getTurnsWithoutMove() {
        return this.count;
    }

    /**
     * This method sets count to zero , if at least one player have a move
     * @return the count
     */
    public void resetTurnsWithoutMove() {
        this.count = 0;
    }
    @Override
    public boolean isGameover() {
        return count == 2 || board.isFull() || !bothPlayerAlive;
    }

    /**
     * Setter for BothPlayerAlive object.
     *
     * @param status
     */
    public void setBothPlayerAlive(boolean status){
        this.bothPlayerAlive = status;
    }

    /**
     * Getter for BothPlayerAlive object.
     *
     * @return true if both players alive, otherwise false
     */
    public boolean getBothPlayerAlive(){
        return this.bothPlayerAlive;
    }

    @Override
    public Player getTurn() {
        if (turnIndex == 0)
            return player1;
        else
            return player2;
    }

    @Override
    public Player getWinner() {
        if (board.getWinnerMark() == Mark.XX)
            return player1;
        else if ((board.getWinnerMark() == Mark.OO))
            return player2;
        //if draw
        return null;
    }

    @Override
    public List<Move> getValidMoves() {
        List<Move> moves = new ArrayList<>();
        Mark currentMark = turnIndex == 0 ? Mark.XX : Mark.OO;
        for (int i = 0; i < board.DIM; i++)
            for (int j = 0; j < board.DIM; j++)
            {
                Move currentMove = new OthelloMove(i, j, currentMark);

                if (isValidMove(currentMove))
                    moves.add(currentMove);
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

        //if DoMove was called, then this move is valid, meaning that at least one opponent's disc should be flipped
        //as indexes of discs(that should be flipped) placed in board.flippedDiscs array
        //so until the size of flippedDisc[] is not zero, we continue to extract each index.
        for (int i = 0; i<this.board.flippedDiscs.size() ; i ++){
            this.board.setField(board.row(board.flippedDiscs.get(i)), board.col(board.flippedDiscs.get(i)), tttm.getMark());
        }
        //change index of player after valid move is done
        turnIndexChange();
    }
    //@ ensures \old(turnIndex) == 0 ==> turnIndex == 1;
    //@ ensures \old(turnIndex) == 1 ==> turnIndex == 0;
    public void turnIndexChange(){
        turnIndex = turnIndex == 0 ? 1 : 0;
        //O for black, 1 for white
    }
    public int getTurnIndex(){
        return turnIndex;
    }
}

