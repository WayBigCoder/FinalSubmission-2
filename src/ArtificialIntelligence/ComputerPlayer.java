package ArtificialIntelligence;

import GameLogic.*;

/**
 * Class for Computer Player
 */
public class ComputerPlayer extends AbstractPlayer {
    private Strategy strategy;
    private String name = "Computer";

    //@ requires strategy != null && (mark == Mark.OO || mark == Mark.XX || mark == Mark.EMPTY);
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(strategy.getName() + " - " + mark);
        this.strategy = strategy;
    }

    public String getName(){
        return name;
    }
    @Override
    public Move determineMove(Game game) {
        return this.strategy.determineMove(game);
    }


}
