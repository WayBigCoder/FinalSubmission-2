package GameLogic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

/**
 * Board for the Othello game.
 */
public class Board {
    /*@ public invariant fields.length == DIM*DIM;
        public invariant (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY || fields[i] == Mark.XX || fields[i] == Mark.OO);
    @*/

    /**
     * Dimension of the board, i.e., if set to 6, the board has 8 rows and 8 columns.
     * Array of flippedDisc, is an array that contains the disc that should be flipped to the opponent's mark
     */
    public static final int DIM = 8;
    private static final String LINE = "---+---+---+---+---+---+---+---";
    public ArrayList<Integer> flippedDiscs;
    /**
     * The DIM by DIM fields of the Othello board.
     */
    public Mark[] fields;

    // -- Constructor --
    /**
     * Creates an empty board and flippedDiscs array.
     * Set centre of the board by default marks.
     */
    //@ ensures (\forall int i; (i >= 0 && i < 27); fields[i] == Mark.EMPTY);
    //@ ensures (\forall int i; (i >= 29 && i < 35); fields[i] == Mark.EMPTY);
    //@ ensures (\forall int i; (i >= 37 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    //@ ensures (fields[27] == Mark.OO && fields[36] == Mark.OO && fields[28] == Mark.XX && fields[35] == Mark.XX);
    public Board() { // XX: black, OO: white
        //creating board with empty fields
        this.fields = new Mark[DIM * DIM];
        Arrays.fill(this.fields, Mark.EMPTY);

        //basic centre at the start of the game
        this.fields[27] = Mark.OO;
        this.fields[28] = Mark.XX;
        this.fields[35] = Mark.XX;
        this.fields[36] = Mark.OO;

        this.flippedDiscs = new ArrayList<>();
    }

    /**
     * Creates a deep copy of this field.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < DIM*DIM); \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {

        Board copyBoard = new Board();
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            copyBoard.fields[i] = this.fields[i];
        }
        return copyBoard;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col) pair.
     * @param row the field's row
     * @param col the field's column
     * @return the index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < DIM;
    requires col >= 0 && row < DIM;
     @*/
    public int index(int row, int col) {
        return (row * DIM + col);
    }

    /**
     * Calculate the row of the board based on the index in the linear array of fields.
     *
     * @param index of the fields
     * @return row of the board
     */
    //@ requires index >= 0 && index < DIM*DIM;
    public int row(int index){
        return (index / DIM);
    }

    /**
     * Calculate the colum of the board based on the index in the linear array of fields.
     * @param index of the fields
     * @return colum of the board
     */
    //@ requires index >= 0 && index < DIM*DIM;
    public int col(int index){
        return (index % DIM);
    }

    /**
     * Getter method
     * @return array of indexes for flipped discs
     */
    public ArrayList<Integer> getFlippedDiscs() { // new
        return flippedDiscs;
    }
    /**
     Check the move for its correctness and what discs will be flipped for this particular move.

     The method go through each direction, starting at the given row and column
     and checking if the next field in that direction is the opponent's mark.
     ---------
     If it is, it adds that field to the list of potential flipped discs and continues checking in
     that direction until it either reaches the current player's mark or an empty field.
     1) If it reaches the current player's mark, the move is considered valid.
     2) If it reaches an empty field or out of boundaries,
     the move is considered invalid and the flipped discs added for that direction are removed from the list.

     @param row The row of the move
     @param col The column of the move
     @param mark The mark of the move
     @return True if the move is valid, false otherwise
     */
    //@ requires isField(row,col) == true && (mark == Mark.XX || mark == Mark.OO || mark == Mark.EMPTY);
    public boolean checkMove(int row, int col, Mark mark) {
        this.flippedDiscs.clear();
        boolean isValid = false;
        //contains all possible directions for checking the move
        //for example: {-1,-1} will check left upper diagonal form the given position
        int[][] directions = { { -1, 1 }, { -1, 0 }, { -1, -1 }, { 0, -1 }, { 0, 1 }, { 1, -1 }, { 1, 0 }, { 1, 1 } };
        Mark opponent = (mark == Mark.XX) ? Mark.OO : Mark.XX;

        for (int[] direction : directions) {
            int numberOfAdd = 0; //count how much potential flipped discs were added for EACH direction
            int row2 = row + direction[0];
            int col2 = col + direction[1];
            if (isField(row2, col2) && this.fields[index(row2, col2)] == opponent) {
                this.flippedDiscs.add(index(row2, col2)); //add discs that could be potentially flipped
                numberOfAdd += 1;
                row2 += direction[0];
                col2 += direction[1];
                while (isField(row2, col2) && this.fields[index(row2, col2)] != mark && this.fields[index(row2, col2)] != Mark.EMPTY) {
                    this.flippedDiscs.add(index(row2, col2));
                    numberOfAdd += 1;

                    row2 += direction[0];
                    col2 += direction[1];
                }
                if (isField(row2, col2) && this.fields[index(row2, col2)] == mark) {
                    isValid = true;
                } else {
                    while(numberOfAdd != 0){
                        //if the move is not valid for specific direction,
                        // then we delete the lasts flipped discs indexes, which were added, for specific direction
                        this.flippedDiscs.remove(this.flippedDiscs.size() - 1);
                        numberOfAdd -= 1;
                    }
                }
            }
        }
        return isValid;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     * @param index of the fields
     * @return true if 0 <= index < DIM*DIM
     */
    //@ ensures index >= 0 && index < DIM*DIM ==> \result == true;
    public boolean isField(int index) {
        return (index >= 0 && index < Board.DIM * Board.DIM);
    }

    /**
     * Returns true if the (row,col) pair refers to a valid field on the board.
     * @param row the field's row
     * @param col the field's column
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    //@ ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    //@ pure
    public boolean isField(int row, int col) {
        return (row >= 0 && row < DIM) && (col >= 0 && col < DIM);
    }

    /**
     * Returns the content of the field i.
     * @param i the number of the field
     * @return the mark on the field
     */
    //@ requires isField(i);
    //@ ensures \result == Mark.EMPTY || \result == Mark.OO || \result == Mark.XX;
    public Mark getField(int i) {
        if (isField(i))
            return fields[i];
        return null;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Mark.EMPTY || \result == Mark.OO || \result == Mark.XX;
     @*/
    public Mark getField(int row, int col) {
        return fields[index(row , col)];
    }

    /**
     * Returns true if the field referred to by the (row,col) pair it empty.
     * @param row the row of the field
     * @param col the column of the field
     * @return true if the field is empty
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {

        return isField(row, col) && getField(row, col) == Mark.EMPTY;
    }

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.XX || fields[i] == Mark.OO);
    public boolean isFull() {
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (fields[i] == Mark.EMPTY) {
                return false;
            }
        }
        return true;
    }


    /**
     * The method calculate the frequency of both marks and return the winner mark.
     * A mark wins if it has more in quantity.
     *
     * @return the mark with the higher frequency. Or Empty Mark in case of draw
     */
    /*@ ensures Collections.frequency(Arrays.asList(fields), Mark.XX) > Collections.frequency(Arrays.asList(fields) , Mark.OO) ==> \result == Mark.XX;
    ensures Collections.frequency(Arrays.asList(fields), Mark.XX) < Collections.frequency(Arrays.asList(fields) , Mark.OO) ==> \result == Mark.OO;
    ensures Collections.frequency(Arrays.asList(fields), Mark.XX) == Collections.frequency(Arrays.asList(fields) , Mark.OO) ==> \result == Mark.EMPTY;
    @*/
    public Mark getWinnerMark() {
        // number of discs for black
        int discX = Collections.frequency(Arrays.asList(fields), Mark.XX);
        // number of discs for white
        int discO = Collections.frequency(Arrays.asList(fields), Mark.OO);
        if ((discO - discX) == 0) {
            return Mark.EMPTY;
        }
        return (Math.max(discO, discX) == discX) ? Mark.XX : Mark.OO;
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as a String
     */
    public String toString() {
        String s = "     ";
        for (int i = 0; i < DIM; i++) {
            s += i + "   ";
        }
        s += "\n";
        for (int i = 0; i < DIM; i++) {
            String row = String.format("%2d", i) + "  ";
            for (int j = 0; j < DIM; j++) {
                row += " " + getField(i, j).toString().substring(0, 1).replace("E", " ") + " ";
                if (j < DIM - 1) {
                    row = row + "|";
                }
            }
            s = s + row;
            if (i < DIM - 1) {
                s = s + "\n" + "    " + LINE  + "\n";
            }
        }
        return s;
    }

    /**
     * Empties all fields of this board (i.e., let them refer to the value Mark.EMPTY).
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public void reset() {

        for (int i = 0; i < (DIM * DIM); i++) {
            fields[i] = Mark.EMPTY;
        }
    }

    /**
     * Sets the content of the field represented by
     * the (row,col) pair to the mark m.
     * @param row the field's row
     * @param col the field's column
     * @param m the mark to be placed
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == m;
     @*/
    public void setField(int row, int col, Mark m) {

        fields[index(row, col)] = m;
    }
}

