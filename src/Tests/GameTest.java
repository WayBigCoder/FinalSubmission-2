package Tests;

import ArtificialIntelligence.*;
import GameLogic.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import java.util.Arrays;
import static org.junit.jupiter.api.Assertions.*;

/**
 * This class contains test cases for the OthelloGame class.
 */
public class GameTest {
    private OthelloGame game;
    private AbstractPlayer player1;
    private AbstractPlayer player2;

    @BeforeEach
    public void setUp() {
        // create a new game with a new board
        player1 = new ComputerPlayer(Mark.XX, new NaiveStrategy());
        player2 = new ComputerPlayer(Mark.OO, new SmartStrategy());
        game = new OthelloGame(player1,player2);
    }

    /**
     * Test case for the isGameover method.
     * It checks the gameover condition when the board is full or both players don't have any valid moves.
     *
     * Example:
     *   0  1  2  3  4  5  6  7
     * 0 O  O  O  O  O  O  O  O
     *  --+--+--+--+--+--+--+--
     * 1 O  O  O  O  O  O  O  O
     *  --+--+--+--+--+--+--+--
     * 2 O  O  O  O  O  O  O  O
     *  --+--+--+--+--+--+--+--
     * 3 O  O  O  O  O  O  O
     *  --+--+--+--+--+--+--+--
     * 4 O  O  O  O  O  O
     *  --+--+--+--+--+--+--+--
     * 5 O  O  O  O  O  O  X
     *  --+--+--+--+--+--+--+--
     * 6 O  O  O  O  O  O  O
     *  --+--+--+--+--+--+--+--
     * 7 0  0  0  0  0  0  0
     *  --+--+--+--+--+--+--+--
     */
    @Test
    public void testGameoverCondition() {

        // Game ends if board is full
        assertFalse(this.game.isGameover());

        Arrays.fill(game.getBoard().fields, Mark.XX);
        assertTrue(this.game.isGameover());

        // game end if both players don't have moves anymore (in the above form)
        Arrays.fill(game.getBoard().fields, Mark.OO);
        this.game.getBoard().setField(3, 7, Mark.EMPTY);
        this.game.getBoard().setField(4, 6, Mark.EMPTY);
        this.game.getBoard().setField(4, 7, Mark.EMPTY);
        this.game.getBoard().setField(5, 7, Mark.EMPTY);
        this.game.getBoard().setField(5, 6, Mark.XX);
        this.game.getBoard().setField(6, 7, Mark.EMPTY);
        this.game.getBoard().setField(7, 7, Mark.EMPTY);

        while (!game.isGameover()) {

            AbstractPlayer currentPlayer = (AbstractPlayer) this.game.getTurn();

            if (this.game.getValidMoves().size() == 0) {
                this.game.turnIndexChange();
                this.game.incrementTurnsWithoutMove();
                continue;
            }
            this.game.resetTurnsWithoutMove();

            Move currentMove = currentPlayer.determineMove(this.game);

            this.game.doMove(currentMove);
        }

        assertTrue(game.isGameover());
    }

    /**
     * Test for full game from beginning to end with random valid moves
     * It tests if the game proceeds correctly with two computer players.
     */
    @Test
    public void testRandomGameplay() {
        // The following
        while (!game.isGameover()) {

            AbstractPlayer currentPlayer = (AbstractPlayer) this.game.getTurn();

            // There can be cases when no moves available,
            // So Test sometimes will not cover line 103 to 110
            if (this.game.getValidMoves().size() == 0) {
                this.game.turnIndexChange();
                this.game.incrementTurnsWithoutMove();

                // count can't be greater than 2
                assertFalse(this.game.getTurnsWithoutMove()>2);

                continue;
            }
            this.game.resetTurnsWithoutMove();

            Move currentMove = currentPlayer.determineMove(this.game);
            assertTrue(game.isValidMove(currentMove)); // check if current move is a valid move

            this.game.doMove(currentMove);

            // ensure that every valid move will always outflank at least 1 disc
            assertTrue(game.getBoard().getFlippedDiscs().size()>0);
        }
        assertTrue(game.isGameover());
    }
}