package ArtificialIntelligence;

import GameLogic.*;

/**
 * The ComputerPlayer class represents a computer player in the game.
 */
public class ComputerPlayer extends AbstractPlayer {
    private Strategy strategy;
    private String name = "Computer";

    /**
     * Constructs a computer player with the specified mark and strategy.
     *
     * @param mark     the mark of the computer player (Mark.OO or Mark.XX)
     * @param strategy the strategy to be used by the computer player
     * @throws IllegalArgumentException if the strategy or mark is invalid
     */
    //@ requires strategy != null && (mark == Mark.OO || mark == Mark.XX || mark == Mark.EMPTY);
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(strategy.getName() + " - " + mark);
        this.strategy = strategy;
    }

    /**
     * Gets the name of the computer player.
     *
     * @return the name of the computer player
     */
    public String getName(){
        return name;
    }

    /**
     * Determines the next move for the computer player using the specified strategy.
     *
     * @param game the current game state
     * @return the determined move
     */
    @Override
    public Move determineMove(Game game) {
        return this.strategy.determineMove(game);
    }


}
