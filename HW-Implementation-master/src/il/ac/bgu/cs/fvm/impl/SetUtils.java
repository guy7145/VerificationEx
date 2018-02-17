package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.util.Pair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class SetUtils {
    @SafeVarargs
    static <X> Set<X> NewSet(X... xs) {
        HashSet<X> set = new HashSet<>();
        for (X x : xs)
            set.add(x);
        return set;
    }

    static <A, B> Set<Pair<A, B>> setProduct(Set<A> s1, Set<B> s2) {
        Set<Pair<A, B>> product = new HashSet<>();
        for (A a : s1)
            for (B b : s2)
                product.add(new Pair<>(a, b));

        return product;
    }

    @SafeVarargs
    static <T> Set<T> union(Set<T>... sets) {
        Set<T> union = new HashSet<>();
        for (Set<T> s : sets)
            union.addAll(s);
        return union;
    }

    static <T> Set<T> difference(Set<T> s1, Set<T> s2) {
        Set<T> result = new HashSet<>();
        result.addAll(s1);
        result.removeAll(s2);
        return result;
    }

    static <T> Set<T> intersect(Set<T> s1, Set<T> s2) {
        Set<T> in = new HashSet<>();
        for (T t : s1)
            if (s2.contains(t))
                in.add(t);
        return in;
    }
}
