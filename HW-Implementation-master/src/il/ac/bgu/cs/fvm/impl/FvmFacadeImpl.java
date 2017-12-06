package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import java.io.InputStream;
import java.util.*;

import static il.ac.bgu.cs.fvm.impl.AddAllUtils.*;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.allOff;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.allPermutations;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.getTrueNames;
import static il.ac.bgu.cs.fvm.impl.SetUtils.difference;
import static il.ac.bgu.cs.fvm.impl.SetUtils.setProduct;
import static il.ac.bgu.cs.fvm.impl.SetUtils.union;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    private <S> void ValidateState(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s)) throw new StateNotFoundException(s);
    }
    private <S> void ValidateStates(TransitionSystem<S, ?, ?> ts, Set<S> ss) {
        for (S s : ss) ValidateState(ts, s);
    }
    private <A> void ValidateAction(TransitionSystem<?, A, ?> ts, A a) {
        if (!ts.getActions().contains(a)) throw new ActionNotFoundException(a);
    }
    private <A> void ValidateActions(TransitionSystem<?, A, ?> ts, Set<A> as) {
        for (A a : as) ValidateAction(ts, a);
    }

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl<>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        for (S state : ts.getStates())
            for (A action : ts.getActions())
                if (post(ts, state, action).size() > 1)
                    return false;

        return ts.getInitialStates().size() <= 1;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        for (S state : ts.getStates()) {
            Set<Set<P>> labels = new HashSet<>();
            for (S s : post(ts, state)) {
                Set<P> l = ts.getLabel(s);
                if (labels.contains(l))
                    return false;
                labels.add(l);
            }
        }
        return ts.getInitialStates().size() <= 1;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isStateTerminal(ts, e.last()) && isInitialExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> restOfExecution = e;
        Set<S> postStates = ts.getStates();

        do {
            S s = restOfExecution.head();
            ValidateState(ts, s);

            if (!postStates.contains(s)) return false;
            if (restOfExecution.tail().isEmpty()) return true;

            A a = restOfExecution.tail().head();
            ValidateAction(ts, a);

            postStates = post(ts, s, a);
            restOfExecution = restOfExecution.tail().tail();
        } while (true);
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isStateTerminal(ts, e.last()) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        ValidateState(ts, s);
        return post(ts, s).size() == 0;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        ValidateState(ts, s);
        Set<S> results = new HashSet<>();
        for (Transition<S, ?> t : ts.getTransitions()) {
            if (t.getFrom().equals(s))
                results.add(t.getTo());
        }
        return results;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        ValidateStates(ts, c);
        Set<S> results = new HashSet<>();
        for (S s : c)
            results.addAll(post(ts, s));

        return results;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        ValidateState(ts, s);
        ValidateAction(ts, a);
        Set<S> results = new HashSet<>();
        for (Transition<S, ?> t : ts.getTransitions()) {
            if (t.getFrom().equals(s) && t.getAction().equals(a))
                results.add(t.getTo());
        }
        return results;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        ValidateStates(ts, c);
        ValidateAction(ts, a);
        Set<S> results = new HashSet<>();
        for (S s : c)
            results.addAll(post(ts, s, a));

        return results;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        ValidateState(ts, s);
        Set<S> results = new HashSet<>();
        for (Transition<S, ?> t : ts.getTransitions()) {
            if (t.getTo().equals(s))
                results.add(t.getFrom());
        }
        return results;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        ValidateStates(ts, c);
        Set<S> results = new HashSet<>();
        for (S s : c)
            results.addAll(pre(ts, s));

        return results;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        ValidateState(ts, s);
        ValidateAction(ts, a);
        Set<S> results = new HashSet<>();
        for (Transition<S, ?> t : ts.getTransitions()) {
            if (t.getTo().equals(s) && t.getAction().equals(a))
                results.add(t.getFrom());
        }
        return results;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        ValidateStates(ts, c);
        ValidateAction(ts, a);
        Set<S> results = new HashSet<>();
        for (S s : c)
            results.addAll(pre(ts, s, a));

        return results;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachables = new HashSet<>();
        Set<S> currentStates = ts.getInitialStates();
        while (currentStates.size() > 0) {
            reachables.addAll(currentStates);
            currentStates = post(ts, currentStates);
            currentStates.removeAll(reachables);
        }
        return reachables;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<>());
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> result = createTransitionSystem();

        result.addAllActions(union(ts1.getActions(), ts2.getActions()));
        result.addAllAtomicPropositions(union(ts1.getAtomicPropositions(), ts2.getAtomicPropositions()));
        result.addAllStates(setProduct(ts1.getStates(), ts2.getStates()));
        for (Pair<S1, S2> s : setProduct(ts1.getInitialStates(), ts2.getInitialStates()))
            result.addInitialState(s);

        Set<A> nonHandshake1 = difference(ts1.getActions(), handShakingActions);
        Set<A> nonHandshake2 = difference(ts2.getActions(), handShakingActions);
        for (Pair<S1, S2> s : result.getStates()) {
            for (A a : handShakingActions) {
                Set<S1> s1Post = post(ts1, s.first, a);
                Set<S2> s2Post = post(ts2, s.second, a);
                for (Pair<S1, S2> postState : setProduct(s1Post, s2Post))
                    result.addTransition(new Transition<>(s, a, postState));
            }
            for (A a : nonHandshake1)
                for (S1 sPost : post(ts1, s.first, a))
                    result.addTransition(new Transition<>(s, a, new Pair<>(sPost, s.second)));
            for (A a : nonHandshake2)
                for (S2 sPost : post(ts2, s.second, a))
                    result.addTransition(new Transition<>(s, a, new Pair<>(s.first, sPost)));
        }
        return result;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<L, A>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> result = createProgramGraph();
        addAllLocationsPG(result, setProduct(pg1.getLocations(), pg2.getLocations()));
        addAllInitialLocationsPG(result, setProduct(pg1.getInitialLocations(), pg2.getInitialLocations()));
        Set<List<String>> initProducts = new HashSet<>();
        for (Pair<List<String>, List<String>> initPair : setProduct(pg1.getInitalizations(), pg2.getInitalizations())) {
            List<String> initProd = new LinkedList<>();
            initProd.addAll(initPair.first);
            initProd.addAll(initPair.second);
            initProducts.add(initProd);
        }
        addAllInitializationsPG(result, initProducts);

        for (L1 l1 : pg1.getLocations()) {
            System.out.println(pg2.getTransitions());
            for (PGTransition<L2, A> t : pg2.getTransitions())
                result.addTransition(
                        new PGTransition<Pair<L1, L2>, A>(
                                new Pair<>(l1, t.getFrom()),
                                t.getCondition(),
                                t.getAction(),
                                new Pair<>(l1, t.getTo())
                        )
                );
        }
        for (L2 l2 : pg2.getLocations())
            for (PGTransition<L1, A> t : pg1.getTransitions())
                result.addTransition(
                        new PGTransition<Pair<L1, L2>, A>(
                                new Pair<>(t.getFrom(), l2),
                                t.getCondition(),
                                t.getAction(),
                                new Pair<>(t.getTo(), l2)
                        )
                );


        return result;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = createTransitionSystem();

        /* auxiliary variable */
        Set<Map<String, Boolean>> allInputPermutations = allPermutations(c.getInputPortNames());
        /* actions */
        ts.addAllActions(allInputPermutations);
        /* initialize initial states */
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> initialStates = new HashSet<>();
        Map<String, Boolean> registersOff = allOff(c.getRegisterNames());
        for (Map<String, Boolean> perm : allInputPermutations)
            initialStates.add(new Pair<>(perm, registersOff));


        /* only reachable states */
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> currentStates = initialStates;
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> post = new HashSet<>();
        do {
            ts.addAllStates(currentStates);

            for (Pair<Map<String, Boolean>, Map<String, Boolean>> s : currentStates)
                for (Map<String, Boolean> action : ts.getActions())
                    post.add(new Pair<>(action, c.updateRegisters(s.first, s.second)));

            currentStates = difference(post, ts.getStates());
            post = new HashSet<>();
        } while (!currentStates.isEmpty());
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> s : initialStates)
            ts.addInitialState(s);

        /* transitions */
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> s : ts.getStates())
            for (Map<String, Boolean> act : ts.getActions())
                ts.addTransition(new Transition<>(s, act, new Pair<>(act, c.updateRegisters(s.first, s.second))));

        /* labels and atomic-propositions */
        for (String x : union(c.getInputPortNames(), c.getRegisterNames(), c.getOutputPortNames()))
            ts.addAtomicProposition(x);

        for (Pair<Map<String, Boolean>, Map<String, Boolean>> s : ts.getStates()) {
            Set<String> label = union(
                    getTrueNames(c.computeOutputs(s.first, s.second)),
                    getTrueNames(s.first),
                    getTrueNames(s.second)
            );
            for (String p : label)
                ts.addToLabel(s, p);
        }
        return ts;
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }

   
}
