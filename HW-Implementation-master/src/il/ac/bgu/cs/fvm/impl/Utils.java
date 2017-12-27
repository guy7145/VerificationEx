package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

import java.util.*;

import static il.ac.bgu.cs.fvm.impl.SetUtils.setProduct;

public class Utils {
    public static <S, A, P> void addAllInitialStatesTS(TransitionSystemImpl<S, A, P> ts, Iterable<S> states) {
        for (S s : states)
            ts.addInitialState(s);
    }
    public static <S, A> void addAllTransitionsTS(TransitionSystem<S, A, ?> ts, Iterable<Transition<S, A>> transitions) {
        for (Transition<S, A> t : transitions)
            ts.addTransition(t);
    }

    public static <L, A> void addAllLocationsPG(ProgramGraph<L, A> pg, Iterable<L> locations) {
        for (L l : locations)
            pg.addLocation(l);
    }
    public static <L, A> void addAllInitialLocationsPG(ProgramGraph<L, A> pg, Iterable<L> locations) {
        for (L l : locations)
            pg.addInitialLocation(l);
    }
    public static <L, A> void addAllInitializationsPG(ProgramGraph<L, A> pg, Iterable<List<String>> initializations) {
        for (List<String> l : initializations)
            pg.addInitalization(l);
    }
    public static <L, A> void addAllTransitionsPG(ProgramGraph<L, A> pg, Iterable<PGTransition<L, A>> transitions) {
        for (PGTransition<L, A> t : transitions)
            pg.addTransition(t);
    }

    private static <T> Set<List<T>> setProductUsingList(Set<List<T>> s1, Set<T> s2) {
        Set<List<T>> product = new HashSet<>();
        for (List<T> l : s1)
            for (T x : s2) {
                List<T> newList = new LinkedList<>();
                newList.addAll(l);
                newList.add(x);
                product.add(newList);
            }
        return product;
    }
    private static <T> Set<List<T>> setProductUsingList(List<Set<T>> sets) {
        Set<List<T>> p = new HashSet<>();
        if (sets.isEmpty())
            return p;

        for (T x : sets.remove(0)) {
            List<T> list = new LinkedList<>();
            list.add(x);
            p.add(list);
        }

        while (!sets.isEmpty())
            p = setProductUsingList(p, sets.remove(0));

        return p;
    }
    public static <L> Set<List<L>> combine(List<Set<L>> sets) {
        return setProductUsingList(new LinkedList<>(sets));
    }

    public static <A> boolean isSyncronizedChannelAction(A action) {
        return action.toString().startsWith("_");
    }

    public static <T> List<T> cloneAndReplace(List<T> list, int index, T newData) {
        List<T> cloned = new LinkedList<>(list);
        cloned.remove(index);
        cloned.add(index, newData);
        return cloned;
    }

    public static <A> boolean isItReallyPossibleAction(Map<String, Object> memoryMap, A action) {
        if (isChannelRead(action)) {
            String cName = getChannelName(action);
            return memoryMap.containsKey(cName) && ((Vector)memoryMap.get(cName)).size() > 0;
        }
        else return true;
    }

    private static <A> String getChannelName(A action) {
        return action.toString().split("\\?")[0];
    }

    private static <A> boolean isChannelRead(A action) {
        return action.toString().contains("?");
    }

    public static class LogicalUtils {
        public static String parenthesis(String x) {
            return String.format("(%s)", x);
        }

        public static String not(String x) {
            return String.format("!%s", x);
        }

        public static String or(String x1, String x2) {
            return String.format("%s || %s", x1, x2);
        }

        public static String and(String x1, String x2) {
            return String.format("%s && %s", x1, x2);
        }

        public static String concatenate(String x1, String x2) {
            return String.format("%s;%s", x1, x2);
        }

        public static boolean isNone(String x) {
            return x.equals("");
        }
    }
}
