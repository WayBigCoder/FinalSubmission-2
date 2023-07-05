package ArtificialIntelligence;

import GameLogic.Game;
import GameLogic.Move;

public interface Strategy {
    /**
     * Getter for name object
     * @return the name of the Strategy
     */
    public String getName();
    public Move determineMove(Game game);

}
