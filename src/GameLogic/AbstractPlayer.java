package GameLogic;

/**
 * AbstractPlayer class representing a player in a game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;

    /**
     * Creates a new Player object.
     *
     * @param name the name of the player
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Returns the name of the player.
     *
     * @return the name
     */
    //@ ensures \result == this.name;
    public String getName() {
        return name;
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's chosen move
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    public abstract Move determineMove(Game game);

    /**
     * Returns a representation of a player, i.e., their name
     *
     * @return the string representation of the player
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}
