package Tests;

import GameLogic.Board;
import GameLogic.Mark;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import java.util.Arrays;
import static org.junit.jupiter.api.Assertions.*;

/**
 * This class contains test cases for the Board class.
 */
public class BoardTest {
    private Board board;

    /**
     * Set up the Board object before each test case.
     */
    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Test case for the Board constructor.
     * It checks if the initial state of the board is set correctly.
     */
    @Test
    public void testBoard(){
        String expectedOutput = "     0   1   2   3   4   5   6   7   \n" +
                " 0     |   |   |   |   |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 1     |   |   |   |   |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 2     |   |   |   |   |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 3     |   |   | O | X |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 4     |   |   | X | O |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 5     |   |   |   |   |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 6     |   |   |   |   |   |   |   \n" +
                "    ---+---+---+---+---+---+---+---\n" +
                " 7     |   |   |   |   |   |   |   ";
        assertEquals(expectedOutput, board.toString());
        // Check the board initial state
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (i == 27 || i == 36) {
                assertEquals(Mark.OO, board.fields[i]);
            } else if (i == 28 || i == 35){
                assertEquals(Mark.XX, board.fields[i]);
            } else {
                assertEquals(Mark.EMPTY, board.fields[i]);
            }
        }
    }

    /**
     * Test case for the isField method.
     * It checks if the given index is a valid index of a field on the board.
     */
    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-100));
        assertFalse(board.isField(101));
        assertTrue(board.isField(0));
        assertTrue(board.isField(Board.DIM * Board.DIM - 1));
        assertFalse(board.isField(Board.DIM * Board.DIM));
    }

    /**
     * Test case for the isField method.
     * It checks if the given row and column are valid on a field of the board.
     */
    @Test
    public void testIsFieldRowCol() {
        // checks if row and col are valid on a field of the board
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertTrue(board.isField(7, 2));
        assertFalse(board.isField(3, 9));
    }

    /**
     * Test case for the setField and getField methods.
     * It checks if setting and getting the field at a specific row and column works correctly.
     */
    @Test
    public void testSetAndGetFieldRowCol() {
        board.setField(5, 5, Mark.XX);
        assertEquals(Mark.XX, board.getField(5, 5));
        assertEquals(Mark.EMPTY, board.getField(0, 1));
        assertEquals(Mark.EMPTY, board.getField(1, 0));
        board.setField(1,1,Mark.OO);
        assertEquals(Mark.OO, board.getField(1, 1));

    }

    /**
     * Test case for the isEmptyField method.
     * It checks if a field at a specific row and column is empty or not.
     */
    @Test
    public void testIsEmptyField(){
        board.setField(0,0,Mark.XX);
        assertFalse(board.isEmptyField(0,0));
        board.setField(0,0,Mark.EMPTY);
        assertTrue(board.isEmptyField(0,0));
    }

    /**
     * Test case for the isFull method.
     * It checks if the whole board is full.
     */
    @Test
    public void testIsFull() {
        //test if the whole board is full
        board.setField(0,1,Mark.XX);
        assertFalse(board.isFull());

        Arrays.fill(board.fields, Mark.XX);
        assertTrue(board.isFull());
    }

    /**
     * Test case for the getField method with index parameter.
     * It checks if the getField method returns the correct mark at the given index.
     */
    @Test
    public void testGetFieldIndex() {
        board.setField(0, 1, Mark.XX);
        assertEquals(Mark.XX, board.getField(1));

        //check the default centre
        assertEquals(Mark.OO, board.getField(27));
        assertEquals(Mark.OO, board.getField(36));

        //check invalid value
        assertEquals(null, board.getField(999));
    }

    /**
     * Test case for the reset method.
     * It checks if all fields are empty after resetting the board.
     */
    @Test
    public void testReset() {
        //after resetting all fields should be empty
        board.setField(1,1,Mark.XX);
        board.setField(2,4,Mark.OO);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(1,1));
        assertEquals(Mark.EMPTY, board.getField(2,4));
    }

    /**
     * Test case for the deepCopy method.
     * It checks if the deep copy of the board is created correctly.
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, 3,Mark.XX);
        board.setField(5, 2,Mark.OO);
        Board deepCopyBoard = board.deepCopy();

        // First test if all the fields are the same
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertEquals(board.getField(i), deepCopyBoard.getField(i));
        }

        // check the fields in the copy are equals to the fields in the original
        assertArrayEquals(board.fields, deepCopyBoard.fields);
    }

    /**
     * Test case for the index method.
     * It checks if the index is calculated correctly for a given row and column.
     */
    @Test
    public void testIndex() {
        // check the index method with various row and column values
        assertEquals(0, board.index(0, 0));
        assertEquals(7, board.index(0, 7));
        assertEquals(8, board.index(1, 0));
        assertEquals(15, board.index(1, 7));
    }

    /**
     * Test case for the row method.
     * It checks if the row is calculated correctly for a given index.
     */
    @Test
    public void testRow() {
        // check the row method with various index values
        assertEquals(0, board.row(0));
        assertEquals(0, board.row(7));
        assertEquals(1, board.row(8));
        assertEquals(1, board.row(15));
    }

    /**
     * Test case for the col method.
     * It checks if the column is calculated correctly for a given index.
     */
    @Test
    public void testCol() {
        // check the col method with various index values
        assertEquals(0, board.col(0));
        assertEquals(7, board.col(7));
        assertEquals(0, board.col(8));
        assertEquals(7, board.col(15));
    }

    /**
     * Test case for the checkMove method.
     * It checks if a move is valid and if opponent's discs are flipped after the move.
     */
    @Test
    public void testCheckMove() {
        // Test the checkMove method with various move values
        /**
         *   0  1  2  3  4  5  6  7
         * 0
         *  --+--+--+--+--+--+--+--
         * 1
         *  --+--+--+--+--+--+--+--
         * 2
         *  --+--+--+--+--+--+--+--
         * 3         o  x
         *  --+--+--+--+--+--+--+--
         * 4         x  o  o  o
         *  --+--+--+--+--+--+--+--
         * 5               o
         *  --+--+--+--+--+--+--+--
         * 6
         *  --+--+--+--+--+--+--+--
         * 7
         *  --+--+--+--+--+--+--+--
         */
        // for example the first move (row 4, col 5, Mark XX),
        // which is valid and after which 1 opponent's disc will be flipped
        assertTrue(board.checkMove(4,5,Mark.XX));
        assertEquals(1, board.getFlippedDiscs().size());
        board.setField(4, 5,Mark.XX);
        board.setField(4,4, Mark.XX);
        // second move is (row 0, col 0, Mark OO),
        // which is not valid and after which 0 opponent's disc will be flipped
        assertFalse(board.checkMove(0,0,Mark.OO));
        assertEquals(0, board.getFlippedDiscs().size());

        assertTrue(board.checkMove(5,5,Mark.OO));
        assertEquals(1, board.getFlippedDiscs().size());
        board.setField(5, 5,Mark.OO);
        board.setField(4,4,Mark.OO);

        assertTrue(board.checkMove(3,2,Mark.XX));
        assertEquals(1, board.getFlippedDiscs().size());
        board.setField(3, 2,Mark.XX);
        board.setField(3, 3,Mark.XX);

        assertTrue(board.checkMove(4,6,Mark.OO));
        assertEquals(1, board.getFlippedDiscs().size());
        board.setField(4, 6,Mark.OO);
        board.setField(4, 5,Mark.OO);

        assertTrue(board.checkMove(4,7,Mark.XX));
        assertEquals(3, board.getFlippedDiscs().size());
        board.setField(4, 7,Mark.XX);
    }

    /**
     * Test case for the getWinnerMark method.
     * It checks if the correct winner mark is returned based on the marks on the board.
     */
    @Test
    public void getWinnerMark() {
        //fill all fields with dark marks
        //the winner should be XX
        Arrays.fill(board.fields, Mark.XX);
        assertEquals(Mark.XX, board.getWinnerMark());

        //fill 2 fields with OO marks and 1 field with XX mark
        //the winner should be OO
        Arrays.fill(board.fields, Mark.EMPTY);
        board.setField(0,1,Mark.OO);
        board.setField(0,2,Mark.OO);
        board.setField(0,3,Mark.XX);
        assertEquals(Mark.OO, board.getWinnerMark());

        //Equal number of marks on the board
        //should return empty mark
        Arrays.fill(board.fields, Mark.EMPTY);
        board.setField(0,1,Mark.OO);
        board.setField(0,2,Mark.XX);
        assertEquals(Mark.EMPTY, board.getWinnerMark());
    }
}