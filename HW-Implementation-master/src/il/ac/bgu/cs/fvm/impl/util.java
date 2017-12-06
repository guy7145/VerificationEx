package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.util.Pair;

import java.util.HashSet;
import java.util.Set;

public class util {
    public static <A, B> Set<Pair<A, B>> setProduct(Set<A> s1, Set<B> s2) {
        Set<Pair<A, B>> product = new HashSet<>();
        for (A a : s1)
            for (B b : s2)
                product.add(new Pair<>(a, b));

        return product;
    }

    public static <T> Set<T> union(Set<T> s1, Set<T> s2) {
        Set<T> union = new HashSet<>();
        union.addAll(s1);
        union.addAll(s2);
        return union;
    }

    public static <T> Set<T> difference(Set<T> s1, Set<T> s2) {
        Set<T> result = new HashSet<>();
        result.addAll(s1);
        result.removeAll(s2);
        return result;
    }
}
