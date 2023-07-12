package ArtificialIntelligence;

import GameLogic.Game;
import GameLogic.Move;

/**
 * The Strategy interface represents a function for determining moves in a game.
 */
public interface Strategy {
    /**
     * Returns the name of the strategy.
     *
     * @return the name of the strategy
     */
    public String getName();

    /**
     * Determines the next move based on the current game state.
     *
     * @param game the current game
     * @return the determined move
     */
    public Move determineMove(Game game);

}
