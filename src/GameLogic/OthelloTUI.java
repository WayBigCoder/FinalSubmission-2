package GameLogic;


import ArtificialIntelligence.ComputerPlayer;
import ArtificialIntelligence.NaiveStrategy;
import ArtificialIntelligence.SmartStrategy;

import java.util.Scanner;

/**
 * TUI for Othello Game
 */
public class OthelloTUI {
    private OthelloGame game;

    /**
     * Creates an OthelloTUI object.
     */
    public OthelloTUI() {}

    /**
     * Constructor that creates a new OthelloTUI with 2 assigned players.
     *
     * @param player1 the first player
     * @param player2 the second player
     */
    public OthelloTUI(AbstractPlayer player1, AbstractPlayer player2) {
        this.game = new OthelloGame(player1, player2);
    }

    /**
     * Checks what type of player (Human or Computer) will be based on their name.
     *
     * @param name the name of the player
     * @param mark the mark of the player
     * @return the player type
     */
    public AbstractPlayer TypeOfPlayer(String name, Mark mark){
        AbstractPlayer player;
        if (name.equals("AI")){
            Scanner sc = new Scanner(System.in);
            System.out.print("Choose the challenge level (Hard or Easy): ");
            String level = sc.nextLine();

            if (level.equals("Hard")){
                // Create a new ComputerPlayer with the given mark and SmartStrategy
                player = new ComputerPlayer(mark, new SmartStrategy());
            }else{
                // Create a new ComputerPlayer with the given mark and NaiveStrategy
                player = new ComputerPlayer(mark, new NaiveStrategy());
            }
        }
        else{
            // Create a new HumanPlayer with the given name and mark
            player = new HumanPlayer(name, mark);
        }

        // Return the created player
        return player;
    }

    /**
     * Asks players for their names and assigns them to player1 and player2.
     *
     * @return an OthelloTUI object with two players
     */
    public OthelloTUI GameWithPlayers() {
        Scanner sc = new Scanner(System.in);
        System.out.print("Enter name for player 1: ");
        String name1 = sc.nextLine();

        // Continue asking for name if it is null or contains only whitespace characters
        while(name1.trim().length() == 0) {
            System.out.println("Name cannot be null! Please enter again!");
            System.out.print("Enter name for player 1: ");
            name1 = sc.nextLine();
        }

        // Create an AbstractPlayer object for player 1
        AbstractPlayer player1 = TypeOfPlayer(name1, Mark.XX);

        System.out.print("Enter name for player 2: ");
        String name2 = sc.nextLine();

        // Continue asking for name if it is null or contains only whitespace characters
        while(name2.trim().length() == 0) {
            System.out.println("Name cannot be null! Please enter again!");
            System.out.print("Enter name for player 2: ");
            name2 = sc.nextLine();
        }

        // Create an AbstractPlayer object for player 2
        AbstractPlayer player2 = TypeOfPlayer(name2, Mark.OO);


        OthelloTUI ticTacToeTUI = new OthelloTUI(player1, player2);
        return ticTacToeTUI;
    }

    /**
     * Runs a game of Othello.
     * It creates an OthelloTUI object and enters a loop that continues until the game is over.

     * In the loop, the method prints the current state of the game board, prompts the current player for their move,
     * updates the game state based on the player's move and checks if the game is over.
     */
    public void run() {
        boolean flag = true;
        while (flag) {
            // Create an instance of OthelloTUI with two players
            OthelloTUI othelloTUI = GameWithPlayers();

            // Loop until the game is over
            while (!othelloTUI.game.isGameover()) {
                // Print the current state of the game board
                System.out.println(othelloTUI.game.getBoard().toString());

                // Get the current player's turn
                AbstractPlayer currentPlayer = (AbstractPlayer) othelloTUI.game.getTurn();
                System.out.println("It's " + currentPlayer.getName() + "'s turn");

                // Check if there are valid moves for the current player
                if(othelloTUI.game.getValidMoves().size() == 0){
                    // No valid moves, change the turn to the next player and increment "count of turns without a move"
                    othelloTUI.game.turnIndexChange();
                    othelloTUI.game.incrementTurnsWithoutMove();
                    continue;
                }
                othelloTUI.game.resetTurnsWithoutMove();

                // Ask the current player for their move
                Move currentMove = currentPlayer.determineMove(othelloTUI.game);

                // Perform the move and update the game state
                othelloTUI.game.doMove(currentMove);
            }

            // Print the winner or indicate a draw
            if (othelloTUI.game.getWinner() != null)
                System.out.println("The winner is: " + othelloTUI.game.getWinner());
            else
                System.out.println("The match is draw!");

            System.out.print("Do u want to play again? (yes/no): ");
            Scanner sc = new Scanner(System.in);
            String playAgain = sc.nextLine();
            if (playAgain.equals("no"))
                flag = false;

            othelloTUI.game.getBoard().reset();
        }
    }

    /**
     * The entry point of the program.
     *
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        OthelloTUI othelloTUI = new OthelloTUI();
        othelloTUI.run();
    }
}