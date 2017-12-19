package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import java.io.InputStream;
import java.util.*;

import static il.ac.bgu.cs.fvm.impl.Utils.*;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.allOff;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.allPermutations;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.getTrueNames;
import static il.ac.bgu.cs.fvm.impl.SetUtils.*;
import static il.ac.bgu.cs.fvm.impl.Utils.isSyncronizedChannelAction;

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
        TransitionSystem<Pair<S1, S2>, A, P> tsInterleaved = createTransitionSystem();

        /* APs, actions and initial states */
        tsInterleaved.addAllActions(union(ts1.getActions(), ts2.getActions()));
        tsInterleaved.addAllAtomicPropositions(union(ts1.getAtomicPropositions(), ts2.getAtomicPropositions()));
        tsInterleaved.addAllStates(setProduct(ts1.getInitialStates(), ts2.getInitialStates()));
        for (Pair<S1, S2> s : tsInterleaved.getStates())
            tsInterleaved.addInitialState(s);

        /* states (reachable) and transitions */
        Set<Pair<S1, S2>> currentStates = tsInterleaved.getInitialStates();
        Set<Pair<S1, S2>> nextStates;
        Set<A> nonHS1 = difference(ts1.getActions(), handShakingActions);
        Set<A> nonHS2 = difference(ts2.getActions(), handShakingActions);
        Set<Transition<Pair<S1, S2>, A>> currentTransitions;
        do {
            nextStates = new HashSet<>();
            currentTransitions = new HashSet<>();
            for (Pair<S1, S2> s : currentStates) {
                for (A a : nonHS1)
                    for (Pair<S1, S2> nextS : setProduct(post(ts1, s.first, a), NewSet(s.second))) {
                        nextStates.add(nextS);
                        currentTransitions.add(new Transition<>(s, a, nextS));
                    }
                for (A a : nonHS2)
                    for (Pair<S1, S2> nextS : setProduct(NewSet(s.first), post(ts2, s.second, a))) {
                        nextStates.add(nextS);
                        currentTransitions.add(new Transition<>(s, a, nextS));
                    }
                for (A a : handShakingActions)
                    for (Pair<S1, S2> nextS : setProduct(post(ts1, s.first, a), post(ts2, s.second, a))) {
                        nextStates.add(nextS);
                        currentTransitions.add(new Transition<>(s, a, nextS));
                    }
            }
            nextStates = difference(nextStates, tsInterleaved.getStates());
            tsInterleaved.addAllStates(nextStates);
            currentStates = nextStates;
            nextStates = null;
            for (Transition<Pair<S1, S2>, A> t : currentTransitions)
                tsInterleaved.addTransition(t);
            currentTransitions = null;
        } while (!currentStates.isEmpty());

        /* labels */
        for (Pair<S1, S2> s : tsInterleaved.getStates())
            for (P p : union(ts1.getLabel(s.first), ts2.getLabel(s.second)))
                tsInterleaved.addToLabel(s, p);

        return tsInterleaved;
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
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = createTransitionSystem();
        Map<String, Object> initialMemory = new HashMap<>();
        /* initial memory mapping */
        Set<Map<String, Object>> initialMemoryMaps = new HashSet<>();
        for (List<String> initList : pg.getInitalizations()) {
            Map<String, Object> mem = new HashMap<>();
            for (String init : initList)
                mem = ActionDef.effect(actionDefs, mem, init);
            initialMemoryMaps.add(mem);
        }
        /* initial states */
        for (Pair<L, Map<String, Object>> s : setProduct(pg.getInitialLocations(), initialMemoryMaps)) {
            ts.addState(s);
            ts.addInitialState(s);
        }
        /* rest states (reachable) */
        Set<Pair<L, Map<String, Object>>> currentStates = ts.getInitialStates();
        Set<Pair<L, Map<String, Object>>> nextStates;
        Set<Transition<Pair<L, Map<String, Object>>, A>> transitions = new HashSet<>();
        Map<L, Set<PGTransition<L, A>>> transitionsOfStates = new HashMap<>();
        for (L l : pg.getLocations())
            transitionsOfStates.put(l, new HashSet<>());
        for (PGTransition<L, A> t : pg.getTransitions())
            transitionsOfStates.get(t.getFrom()).add(t);
        do {
            nextStates = new HashSet<>();
            for (Pair<L, Map<String, Object>> s : currentStates) {
                for (PGTransition<L, A> t : transitionsOfStates.getOrDefault(s.first, new HashSet<>()))
                    if (ConditionDef.evaluate(conditionDefs, s.second, t.getCondition())) {
                        Pair<L, Map<String, Object>> dst = new Pair<>(t.getTo(), ActionDef.effect(actionDefs, s.second, t.getAction()));
                        nextStates.add(dst);
                        transitions.add(new Transition<>(s, t.getAction(), dst));
                    }
            }
            nextStates = difference(nextStates, ts.getStates());
            ts.addAllStates(nextStates);
            currentStates = nextStates;
        } while (!currentStates.isEmpty());

        /* transitions and actions */
        for (Transition<Pair<L, Map<String, Object>>, A> t : transitions) {
            ts.addAction(t.getAction());
            ts.addTransition(t);
        }

        /* aps and labels */
        for (Pair<L, Map<String, Object>> s : ts.getStates()) {
            ts.addAtomicProposition(s.first.toString());
            ts.addToLabel(s, s.first.toString());
            for (Map.Entry<String, Object> entry : s.second.entrySet()) {
                String ap = String.format("%s = %s", entry.getKey(), entry.getValue().toString());
                ts.addAtomicProposition(ap);
                ts.addToLabel(s, ap);
            }
        }
        return ts;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts = new TransitionSystemImpl<>();
        ActionDef actDef = new ParserBasedActDef();
        ConditionDef condDef = new ParserBasedCondDef();
        InterleavingActDef handShakesDef = new ParserBasedInterleavingActDef();

        //region INITIAL STATES (COMBINING INITIAL LOCATIONS AND MEMORY)
        //region location and initialization products
        /* initial locations product */
        List<Set<L>> discreteInitialLocations = new LinkedList<>();
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs())
            discreteInitialLocations.add(pg.getInitialLocations());
        Set<List<L>> initialLocations = combine(discreteInitialLocations);

        /* initializations product */
        List<Set<List<String>>> pgInits = new LinkedList<>();
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
            if (pg.getInitalizations().size() > 0)
                pgInits.add(pg.getInitalizations());
        }
        Set<List<List<String>>> initProducts = combine(pgInits);
        //endregion

        //region initial memories
        Set<Map<String, Object>> initialMemoryMaps = new HashSet<>();
        if (initProducts.size() == 0)
            initialMemoryMaps.add(new HashMap<>());
        else for (List<List<String>> singleInitProduct : initProducts) {
            Map<String, Object> memoryMap = new HashMap<>();
            for (List<String> singlePgInit : singleInitProduct)
                for (String init : singlePgInit)
                    memoryMap = actDef.effect(memoryMap, init);
            initialMemoryMaps.add(memoryMap);
        }
        //endregion

        Set<Pair<List<L>, Map<String, Object>>> initialStates = setProduct(initialLocations, initialMemoryMaps);
        ts.addAllStates(initialStates);
        initialStates.forEach(ts::addInitialState);
        //endregion

        // region REST STATES (REACHABLE)
        //region transition and action mappings
        Map<ProgramGraph<L, A>, Map<A, PGTransition<L, A>>> pgToSimultaneousActionsToTransitions = new HashMap<>();
        Map<ProgramGraph<L, A>, Map<L, Set<PGTransition<L, A>>>> pgToLocationToTransitions = new HashMap<>();

        for (ProgramGraph<L, A> pg : cs.getProgramGraphs())
            pgToSimultaneousActionsToTransitions.put(pg, new HashMap<>());

        for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
            /* create the mapping of the PG */
            Map<L, Set<PGTransition<L, A>>> transitionsOfLocations = new HashMap<>();
            pgToLocationToTransitions.put(pg, transitionsOfLocations);

            /* initialize mappings for locations and put the transitions in the map */
            for (L l : pg.getLocations())
                transitionsOfLocations.put(l, new HashSet<>());
            for (PGTransition<L, A> t : pg.getTransitions()) {
                transitionsOfLocations.get(t.getFrom()).add(t);
                if (isSyncronizedChannelAction(t.getAction())) {
                    pgToSimultaneousActionsToTransitions.get(pg).put(t.getAction(), t);
                }
            }
        }

        List<Pair<ProgramGraph<L, A>, Set<A>>> pgToSimActions = new LinkedList<>();
        pgToSimultaneousActionsToTransitions.forEach((key, value) -> pgToSimActions.add(new Pair<>(key, value.keySet())));
        Set<List<Pair<ProgramGraph<L, A>, A>>> simActionsProduct = setProductUsingPairList(pgToSimActions);
        //endregion


        Set<Pair<List<L>, Map<String, Object>>> currentStates = ts.getInitialStates();
        Set<Pair<List<L>, Map<String, Object>>> nextStates;
        Set<Transition<Pair<List<L>, Map<String, Object>>, A>> reachableTransitions = new HashSet<>();

        do {
            nextStates = new HashSet<>();
            for (Pair<List<L>, Map<String, Object>> currentState : currentStates) {
                for (int i = 0; i < currentState.first.size(); i++) {
                    L currentLocationPg = currentState.first.get(i);
                    ProgramGraph<L, A> pg = cs.getProgramGraphs().get(i);

                    for (PGTransition<L, A> currentTransition : pgToLocationToTransitions.get(pg).get(currentLocationPg)) {
                        if (condDef.evaluate(currentState.second, currentTransition.getCondition())) {
                            A currentAction = currentTransition.getAction();
                            if (isSyncronizedChannelAction(currentAction)) {
                                //region simultaneous
                                for (List<Pair<ProgramGraph<L, A>, A>> pgAndSimActions : simActionsProduct) // for each possibility of simultaneous actions
                                    if (hasActionOfPg(currentAction, pg, pgAndSimActions)) { // only if the possibility refers to the current action
                                        // pickup some other action and if possible commit both actions together
                                        for (int j = 0; j < pgAndSimActions.size(); j++) {
                                            ProgramGraph<L, A> otherPg = pgAndSimActions.get(j).first;
                                            A otherAction = pgAndSimActions.get(j).second;
                                            if (!otherPg.equals(pg))
                                                if (isReadWriteActions(currentAction, otherAction)) {
                                                    A interleavedAction = interleaveActions(i, j, currentAction, pgAndSimActions.get(j).second);
                                                    Pair<List<L>, Map<String, Object>> nextState = new Pair<>(
                                                            cloneAndReplace(
                                                                    cloneAndReplace(currentState.first, i, currentTransition.getTo()),
                                                                    j,
                                                                    pgToSimultaneousActionsToTransitions
                                                                            .get(otherPg)
                                                                            .get(otherAction)
                                                                            .getTo()),
                                                            handShakesDef.effect(currentState.second, interleavedAction)
                                                    );
                                                    nextStates.add(nextState);
                                                    reachableTransitions.add(new Transition<>(currentState, interleavedAction, nextState));
                                                }
                                        }
                                    }
                                //endregion
                            } else
                                //region non-simultaneous
                                if (isItReallyPossibleAction(currentState.second, currentTransition.getAction())) {
                                    Pair<List<L>, Map<String, Object>> nextState = new Pair<>(
                                            cloneAndReplace(currentState.first, i, currentTransition.getTo()),
                                            actDef.effect(currentState.second, currentAction)
                                    );

                                    nextStates.add(nextState);
                                    reachableTransitions.add(new Transition<>(currentState, currentAction, nextState));
                                }
                                //endregion
                        }
                    }
                }
            }

            //region (loop step)
            nextStates = difference(nextStates, ts.getStates());
            ts.addAllStates(nextStates);
            currentStates = nextStates;
            //endregion
        } while (!currentStates.isEmpty());
        //endregion

        //region TRANSITIONS & ACTIONS
        // actions
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs())
            for (PGTransition<L, A> t : pg.getTransitions())
                ts.addAction(t.getAction());

        for (Transition<Pair<List<L>, Map<String, Object>>, A> t : reachableTransitions) {
            ts.addAction(t.getAction());
            ts.addTransition(t);
        }
        //endregion

        //region APS & LABELS
        for (Pair<List<L>, Map<String, Object>> s : ts.getStates()) {
            for (L location : s.first) {
                ts.addAtomicProposition(location.toString());
                ts.addToLabel(s, location.toString());
            }
            for (Map.Entry<String, Object> entry : s.second.entrySet()) {
                String ap = String.format("%s = %s", entry.getKey(), entry.getValue().toString());
                ts.addAtomicProposition(ap);
                ts.addToLabel(s, ap);
            }
        }
        //endregion

        return ts;
    }

    private <L, A> boolean hasActionOfPg(A action, ProgramGraph<L, A> pg, List<Pair<ProgramGraph<L, A>, A>> simulActions) {
        for (Pair<ProgramGraph<L, A>, A> pair : simulActions) {
            if (pair.first.equals(pg))
                return pair.second.equals(action);
        }
        return false;
    }

    private static <K, T> Set<List<Pair<K, T>>> setProductUsingPairList(Set<List<Pair<K, T>>> s1, Pair<K, Set<T>> s2) {
        Set<List<Pair<K, T>>> product = new HashSet<>();
        for (List<Pair<K, T>> l : s1)
            for (T x : s2.second) {
                List<Pair<K, T>> newList = new LinkedList<>();
                newList.addAll(l);
                newList.add(new Pair<>(s2.first, x));
                product.add(newList);
            }
        return product;
    }
    private static <K, T> Set<List<Pair<K, T>>> setProductUsingPairList(List<Pair<K, Set<T>>> sets) {
        sets = new LinkedList<>(sets);
        Set<List<Pair<K, T>>> p = new HashSet<>();
        for (int i = sets.size() - 1; i >= 0; i--)
            if (sets.get(i).second.isEmpty())
                sets.remove(i);

        if (sets.isEmpty())
            return p;
        Pair<K, Set<T>> firstPair = sets.remove(0);
        for (T x : firstPair.second) {
            List<Pair<K, T>> list = new LinkedList<>();
            list.add(new Pair<>(firstPair.first, x));
            p.add(list);
        }
        while (!sets.isEmpty())
            p = setProductUsingPairList(p, sets.remove(0));

        return p;
    }

    private <A> A interleaveActions(int i, int j, A ai, A aj) {
        if (i < j)
            return (A) (ai.toString() + "|" + aj.toString());
        else
            return (A) (aj.toString() + "|" + ai.toString());
    }

    private <A> boolean isReadWriteActions(A a1, A a2) {
        String first = a1.toString();
        String second = a2.toString();

        if(first.contains("?") && second.contains("!")){
            String chanName1 = first.split("\\?")[0];
            String chanName2 = second.split("\\!")[0];
            return chanName1.equals(chanName2);
        }
        if(first.contains("!") && second.contains("?")){
            String chanName1 = first.split("\\!")[0];
            String chanName2 = second.split("\\?")[0];
            return chanName1.equals(chanName2);
        }
        return false;
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
