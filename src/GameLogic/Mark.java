package GameLogic;

/**
 * Represents a mark in the Othello game.
 * There are three possible values: Mark.XX (black), Mark.OO (white), and Mark.EMPTY.
 */
public enum Mark {
    EMPTY, XX, OO; // XX: black, OO: white

    /**
     * Returns the other mark.
     *
     * @return the other mark if this mark is not EMPTY, otherwise EMPTY
     */
    //@ ensures this == XX ==> \result == OO && this == OO ==> \result == XX;
    public Mark other() {
        if (this == XX) {
            return OO;
        } else if (this == OO) {
            return XX;
        } else {
            return EMPTY;
        }
    }
}
