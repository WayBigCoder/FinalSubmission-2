package GameLogic;

/**
 * OthelloMove class representing a move in an Othello game.
 * Implements the Move interface.
 */
public class OthelloMove implements Move {
    private Mark mark;
    private int row;
    private int col;

    /**
     * Constructs an OthelloMove object with the given row, column, and mark.
     *
     * @param row  the row of the move
     * @param col  the column of the move
     * @param mark the mark (X or O) of the move
     */
    public OthelloMove(int row, int col, Mark mark) {
        this.row = row;
        this.col = col;
        this.mark = mark;
    }

    /**
     * Returns the mark associated with the move.
     *
     * @return the mark (X or O) associated with the move
     */
    public Mark getMark() {
        return mark;
    }

    /**
     * Returns the row on which the move is made.
     * @return row
     */
    public int getRow() {
        return row;
    }

    /**
     * Returns the col on which the move is made.
     *
     * @return col
     */
    public int getCol() {
        return col;
    }

    /**
     * Returns a string representation of the move.
     *
     * @return a string representation of the move
     */
    public String toString() {
        String s = ("Row " + this.row + " - Col " + this.col + " - Mark " + this.mark);
        return s;
    }
}
