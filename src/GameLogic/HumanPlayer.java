package GameLogic;


import java.util.Scanner;

/**
 * Player class for real player.
 */
public class HumanPlayer extends AbstractPlayer {
    /**
     * Mark of a player.
     */
    private Mark mark;
    /**
     * Creates a new Player object.
     *
     * @param name of the player
     * @param mark of the player
     */
    public HumanPlayer(String name, Mark mark) {
        super(name);
        this.mark = mark;
    }

    /**
     * Return the mark of a player.
     * @return mark of a player
     */
    public Mark getMark() {
        return this.mark;
    }

    /**
     * Determines the next move for the human player by asking it.
     *
     * @param game the current game
     * @return Move of the player's choice
     */
    @Override
    public Move determineMove(Game game) {
        while (true) {
            System.out.print("Enter a valid move (row col): ");

            Scanner sc = new Scanner(System.in);
            String line = sc.nextLine();

            while (!isValidMoveFormat(line)) {
                System.out.println("Invalid move format! Please enter again.");
                System.out.print("Enter a valid move (row col): ");

                line = sc.nextLine();
            }
            String[] parse = line.split(" ");
            int row = Integer.parseInt(parse[0]);
            int col = Integer.parseInt(parse[1]);

            Move move = new OthelloMove(row, col, getMark());
            if (game.isValidMove(move)) {
                return move;
            } else {
                System.out.println("Move is not valid! Please enter again!\n");
            }
        }
    }

    /**
     * Validates the format of a move input string.
     *
     * @param move The move input string to validate.
     * @return true if the move format is valid, false otherwise.
     */
    private static boolean isValidMoveFormat(String move) {
        String[] coordinates = move.split(" ");
        if (coordinates.length != 2) {
            return false;
        }
        try {
            //check if row and col are Integer type
            Integer.parseInt(coordinates[0]);
            Integer.parseInt(coordinates[1]);
            return true;
        } catch (NumberFormatException e) {
            return false;
        }
    }
}
