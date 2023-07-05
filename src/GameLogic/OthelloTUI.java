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

    public OthelloTUI() {}
    // constructor for 2 Abstract Players

    /**
     * Constructor that creates a new OthelloTUI with 2 assigned players
     * @param player1
     * @param player2
     */
    public OthelloTUI(AbstractPlayer player1, AbstractPlayer player2) {
        this.game = new OthelloGame(player1, player2);
    }

    /**
     * check what type of player will be based on his name : Human or Computer(if -S or -N)
     * @param name of the player
     * @param mark his mark
     * @return the player type
     */
    public AbstractPlayer TypeOfPlayer(String name, Mark mark){
        AbstractPlayer player;
        if (name.equals("AI")){
            Scanner sc = new Scanner(System.in);
            System.out.print("Choose the challenge level (Hard or Easy): ");
            String level = sc.nextLine();
            if (level.equals("Hard")){
                player = new ComputerPlayer(mark, new SmartStrategy());
            }else{
                player = new ComputerPlayer(mark, new NaiveStrategy());
            }
        }
        else{
            player = new HumanPlayer(name, mark);}

        return player;
    }

    /**
     * This method ask players for their names and assign each to player1 and player2
     * @return OthelloTUI with two parameters (AbstractPlayer player1, AbstractPlayer player2)
     */
    public OthelloTUI GameWithPlayers() {
        Scanner sc = new Scanner(System.in);
        System.out.print("Enter name for player 1: ");
        String name1 = sc.nextLine();

        while(name1.trim().length() == 0) {
            System.out.println("Name cannot be null! Please enter again!");
            System.out.print("Enter name for player 1: ");
            name1 = sc.nextLine();
        }
        AbstractPlayer player1 = TypeOfPlayer(name1, Mark.XX);

        System.out.print("Enter name for player 2: ");
        String name2 = sc.nextLine();
        while(name2.trim().length() == 0) {
            System.out.println("Name cannot be null! Please enter again!");
            System.out.print("Enter name for player 2: ");
            name2 = sc.nextLine();
        }
        AbstractPlayer player2 = TypeOfPlayer(name2, Mark.OO);


        OthelloTUI ticTacToeTUI = new OthelloTUI(player1, player2);
        return ticTacToeTUI;
    }
    /**
     * This method, used in the MAIN, runs a game of Othello.
     * It creates an instance of the OthelloTUI class and enters a loop that continues until the game is over.
     * ---
     * In the loop,
     * the method prints the current state of the game board, prompts the current player for their move,
     * updates the game state based on the player's move, and checks if the game is over.
     *
     */
    public void run() {
        boolean flag = true;
        while (flag) {
            //GameWithPlayers() returns --> TicTacToeTUI(player1, player2)
            OthelloTUI othelloTUI = GameWithPlayers();

            while (!othelloTUI.game.isGameover()) {
                // print the board
                System.out.println(othelloTUI.game.getBoard().toString());

                //return the player(whose turn it is) player1 or player2
                AbstractPlayer currentPlayer = (AbstractPlayer) othelloTUI.game.getTurn();
                System.out.println("It's " + currentPlayer.getName() + "'s turn");

                //if no potential moves for a player, then we turnIndex for the next player
                //and increase a count number
                //(if count number reaches 2, then it means both players don't have moves, so the game will be over)
                if(othelloTUI.game.getValidMoves().size() == 0){
                    othelloTUI.game.turnIndexChange();
                    othelloTUI.game.incrementTurnsWithoutMove();
                    continue;
                }
                othelloTUI.game.resetTurnsWithoutMove();
                //ask player for move
                Move currentMove = currentPlayer.determineMove(othelloTUI.game);

                //doMove -(in doMove the turn_index is changed for next player)-
                othelloTUI.game.doMove(currentMove);



            }
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

    public static void main(String[] args) {
        OthelloTUI othelloTUI = new OthelloTUI();
        othelloTUI.run();
    }
}