package il.ac.bgu.cs.fvm.impl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class CircuitUtils {
    private static void nextPerm(boolean[] perm) {
        for (int i = 0; i < perm.length; i++) {
            if (!perm[i]) {
                perm[i] = true;
                return;
            } else perm[i] = false;
        }
    }
    private static Map<String, Boolean> namesAndValuesToMapping(Set<String> names, boolean[] values) {
        Map<String, Boolean> mapping = new HashMap<>();
        int i = 0;
        for (String name : names) {
            mapping.put(name, values[i]);
            i++;
        }
        return mapping;
    }
    public static Set<Map<String, Boolean>> allPermutations(Set<String> xs) {
        Set<Map<String, Boolean>> results = new HashSet<>();
        int inputDimension = xs.size();
        boolean[] accumulator = new boolean[inputDimension];

        for (int i = 0; i < Math.pow(2, inputDimension); i++) {
            results.add(namesAndValuesToMapping(xs, accumulator));
            nextPerm(accumulator);
        }
        return results;
    }
    public static Set<String> getTrueNames(Map<String, Boolean> map) {
        Set<String> names = new HashSet<>();
        map.forEach((name, val) -> {if (val) names.add(name);});
        return names;
    }
    public static Map<String, Boolean> allOff(Set<String> names) {
        return namesAndValuesToMapping(names, new boolean[names.size()]);
    }
}
