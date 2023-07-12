package util;

import GameLogic.Board;

import java.util.ArrayList;
import java.util.List;

/**
 * The Mapping class provides methods for converting between coordinates and indices.
 */
public class Mapping {

    /**
     * Converts the given coordinates to an index based on the board dimensions.
     *
     * @param x the x-coordinate
     * @param y the y-coordinate
     * @return the corresponding index
     */
    public int fromCoordinateToInt(int x, int y) {
        return x * Board.DIM + y;
    }

    /**
     * Converts the given index to coordinates based on the board dimensions.
     *
     * @param idx the index
     * @return a list containing the x and y coordinates
     */
    public List<Integer> fromIntToCoordinate(int idx) {
        ArrayList<Integer> res = new ArrayList<>();

        int x = idx / Board.DIM;
        int y = idx - x*Board.DIM;

        res.add(x);
        res.add(y);

        return res;
    }
}
