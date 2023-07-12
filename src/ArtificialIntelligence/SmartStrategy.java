package ArtificialIntelligence;

import GameLogic.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The SmartStrategy class inherits the Strategy interface and represents
 * a smart strategy for determining moves in a game.
 */
public class SmartStrategy implements Strategy{
    private final String name = "Smart";

    /**
     * Returns the name of the strategy.
     *
     * @return the name of the strategy
     */
    @Override
    public String getName() {
        return name;
    }

    /**
     * Determines the next move based on the current game state using a smart strategy.
     * The smart strategy selects the move that results in the maximum number of flipped discs.
     *
     * @param game the current game
     * @return the determined move
     */
    @Override
    public Move determineMove(Game game) {
        // List of all valid moves
        List<Move> allMoves = game.getValidMoves();
        ArrayList<Integer> numberOfFlips = new ArrayList<>();

        // Determine the number of flipped discs for each valid move
        for (Move move: allMoves){
            game.isValidMove(move);
            numberOfFlips.add(game.getBoard().getFlippedDiscs().size());
        }

        // Find the maximum number of flipped discs
        int maxNumberFlips = Collections.max(numberOfFlips);
        int indexForBestMove = numberOfFlips.indexOf(maxNumberFlips);

        // Select the move with the maximum number of flipped discs as the best move
        Move bestMove = allMoves.get(indexForBestMove);
        System.out.println(bestMove.toString());

        // Check if the best move is still valid and return it
        if (game.isValidMove(bestMove))
            return bestMove;
        return null;
    }
}
