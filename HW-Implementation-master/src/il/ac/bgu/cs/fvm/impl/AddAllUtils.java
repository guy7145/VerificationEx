package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.List;

public class AddAllUtils {
    public static <S, A, P> void addAllInitialStatesTS(TransitionSystemImpl<S, A, P> ts, Iterable<S> states) {
        for (S s : states)
            ts.addInitialState(s);
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
}
