package ArtificialIntelligence;

import GameLogic.Game;
import GameLogic.Move;

import java.util.List;
import java.util.Random;

/**
 * The NaiveStrategy class inherits the Strategy interface and represents
 * a naive strategy for determining moves in a game.
 */
public class NaiveStrategy implements Strategy {
    private final String name = "Naive";

    /**
     * Gets the name of the naive strategy.
     *
     * @return the name of the naive strategy
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Determines the next move based on the current game state using a naive strategy.
     * The naive strategy selects a random move from the list of valid moves.
     *
     * @param game the current game
     * @return the determined move
     */
    @Override
    public Move determineMove(Game game) {
        List<Move> allMoves = game.getValidMoves();

        // Generate a random index within the range of available moves
        Random rand = new Random();
        int index = rand.nextInt(allMoves.size());

        // Retrieve a random move from the list of available moves
        Move randomMove = allMoves.get(index);

        // Check if the randomly selected move is valid and return it, otherwise null returned
        if (game.isValidMove(randomMove)) {
            System.out.println("Computer move is " + randomMove.toString());
            return randomMove;
        } else {
            return null;
        }
    }
}
