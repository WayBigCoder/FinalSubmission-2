package util;

import GameLogic.Board;

import java.util.ArrayList;
import java.util.List;

public class Mapping {
    public int fromCoordinateToInt(int x, int y) {
        return x * Board.DIM + y;
    }

    public List<Integer> fromIntToCoordinate(int idx) {
        ArrayList<Integer> res = new ArrayList<>();

        int x = idx / Board.DIM;
        int y = idx - x*Board.DIM;

        res.add(x);
        res.add(y);

        return res;
    }
}
