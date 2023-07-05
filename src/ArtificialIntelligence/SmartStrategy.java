package ArtificialIntelligence;

import GameLogic.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Class for identifying the best move for AI
 */
public class SmartStrategy implements Strategy{
    private final String name = "Smart";

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Move determineMove(Game game) {
        List<Move> allMoves = game.getValidMoves();
        ArrayList<Integer> numberOfFlips = new ArrayList<>();
        for (Move move: allMoves){
            game.isValidMove(move);
            numberOfFlips.add(game.getBoard().getFlippedDiscs().size());
        }
        int maxNumberFlips = Collections.max(numberOfFlips);
        int indexForBestMove = numberOfFlips.indexOf(maxNumberFlips);
        Move bestMove = allMoves.get(indexForBestMove);
        System.out.println(bestMove.toString());
        if (game.isValidMove(bestMove))
            return bestMove;
        return null;
    }
}
