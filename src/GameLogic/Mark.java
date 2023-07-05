package GameLogic;

public enum Mark {
    /**
     * Represents a mark in the Othello game. There three possible values:
     * Mark.XX (black), Mark.OO (white) and Mark.EMPTY.
     */
    EMPTY, XX, OO; // XX: black, OO: white

    /**
     * Returns the other mark.
     * @return the other mark is this mark is not EMPTY or EMPTY
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
