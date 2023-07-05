package ArtificialIntelligence;

import GameLogic.Game;
import GameLogic.Move;

import java.util.List;
import java.util.Random;

/**
 * One type of the Strategy, called Naive
 */
public class NaiveStrategy implements Strategy {
    private final String name = "Naive";

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public Move determineMove(Game game) {
        List<Move> allMoves = game.getValidMoves();
        Random rand = new Random();
        int index = rand.nextInt(allMoves.size());
        Move randomMove = allMoves.get(index);

        if (game.isValidMove(randomMove)){
            System.out.println("Computer move is "+ randomMove.toString());
            return randomMove;
        }
        return null;
    }
}
