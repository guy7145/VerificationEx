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
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.io.InputStream;
import java.util.*;

import static il.ac.bgu.cs.fvm.impl.Utils.*;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.allOff;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.allPermutations;
import static il.ac.bgu.cs.fvm.impl.CircuitUtils.getTrueNames;
import static il.ac.bgu.cs.fvm.impl.SetUtils.*;
import static il.ac.bgu.cs.fvm.impl.Utils.LogicalUtils.*;
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
        if (initialMemoryMaps.isEmpty())
            initialMemoryMaps.add(new HashMap<>());
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
        TransitionSystem<Pair<Sts, Saut>, A, Saut> result = createTransitionSystem();

        for (Sts s1 : ts.getStates())
            for (Saut s2 : aut.getTransitions().keySet())
                result.addState(new Pair<>(s1, s2));

        for (Sts s1 : ts.getInitialStates())
            for (Saut s2 : aut.getInitialStates())
                for (Saut s3 : aut.getTransitions().get(s2).get(ts.getLabel(s1)))
                    result.addInitialState(new Pair<>(s1, s3));

        result.addAllActions(ts.getActions());

        for (Transition<Sts, A> t : ts.getTransitions())
            for (Saut s1 : aut.getTransitions().keySet())
                if (aut.getTransitions().get(s1).get(ts.getLabel(t.getTo())) != null)
                    for (Saut s2 : aut.getTransitions().get(s1).get(ts.getLabel(t.getTo())))
                        result.addTransitionFrom(new Pair<>(t.getFrom(), s1)).action(t.getAction()).to(new Pair<>(t.getTo(), s2));

        removeUnreachableStates(result);

        result.getStates().forEach(s -> {
            result.addAtomicProposition(s.second);
            result.addToLabel(s, s.second);
        });

        return result;
    }

    private <S1, S2, A, P> void removeUnreachableStates(TransitionSystem<Pair<S1, S2>, A, P> ts) {
        Set<Pair<S1,S2>> reachable = reach(ts);
        Set<Pair<S1,S2>> removeStates = new HashSet<>();
        for (Pair<S1,S2> s : ts.getStates())
            if (!reachable.contains(s)) {
                Set<Transition<Pair<S1, S2>, A>> removeTransition = new HashSet<>();
                for (Transition<Pair<S1, S2>, A> t : ts.getTransitions())
                    if (s.equals(t.getFrom()) || s.equals(t.getTo()))
                        removeTransition.add(t);
                removeTransition.forEach(ts::removeTransition);
                ts.getLabel(s).forEach(p -> ts.removeLabel(s, p));
                removeStates.add(s);
            }
        removeStates.forEach(ts::removeState);
    }


    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        return  programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaFile(filename));
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        return  programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaString(nanopromela));
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        return  programGraphFromNanoPromela(NanoPromelaFileReader.parseNanoPromelaStream(inputStream));
    }

    private ProgramGraph<String, String> programGraphFromNanoPromela(StmtContext sc) {
        ProgramGraph<String, String> pg= createProgramGraph();
        List<PGTransition<String,String>> transitions = generateTransitionsFromStatements(sc,false);

        pg.addInitialLocation(sc.getText());
        for (PGTransition<String,String> tran: transitions) {
            if(!isNone(tran.getFrom()))
                pg.addLocation(tran.getFrom());

            pg.addLocation(tran.getTo());
            pg.addTransition(tran);
        }
        return pg;
    }

    private List<PGTransition<String,String>> generateTransitionsFromStatements(StmtContext root, boolean ifStatementHappend) {
        List<PGTransition<String, String>> resultTransitions = new ArrayList<>();
        //region basic case
        if(root.assstmt() != null || root.skipstmt() != null || root.atomicstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null){
 			/* The sub statements are only <root> and <exit> */
            if(ifStatementHappend) {
                String action = root.getText();
                PGTransition<String, String> pgTrans = new PGTransition<>("","",action,"");
                resultTransitions.add(pgTrans);
            } else {
                String from = root.getText();
                PGTransition<String, String> pgTrans = new PGTransition<>(from,"",from,"");
                resultTransitions.add(pgTrans);
            }
            return resultTransitions;
        }
        //endregion
        //region if-statement
        NanoPromelaParser.IfstmtContext ifstmt;
        if((ifstmt = root.ifstmt())!=null){
			/* The sub-statements are [root], [exit], and the sub-statements of all op.stmt() where opis a member of root.ifstmt().option()*/
            for(NanoPromelaParser.OptionContext oc : ifstmt.option()){
                List<PGTransition<String, String>> subTransToAdd;
                subTransToAdd = generateTransitionsFromStatements(oc.stmt(), true);
                for(PGTransition<String, String> pgTrans : subTransToAdd){
                    if(!ifStatementHappend){
                        if(isNone(pgTrans.getFrom()))
                            pgTrans.setFrom(ifstmt.getText());
                    }
                    if(pgTrans.getFrom().equals(ifstmt.getText()) || isNone(pgTrans.getFrom())){
                        if(isNone(pgTrans.getCondition()))
                            pgTrans.setCondition(parenthesis(oc.boolexpr().getText()));
                        else pgTrans.setCondition(and(parenthesis(oc.boolexpr().getText()), parenthesis(pgTrans.getCondition())));
                    }
                }
                resultTransitions.addAll(subTransToAdd);
            }
            return resultTransitions;
        }
        //endregion
        //region do-statement
        NanoPromelaParser.DostmtContext dostmt;
        if((dostmt = root.dostmt()) != null) {
			/* The sub-statements are [root], [exit], and locations [;root] where is a sub-statement of some opin root.dostmt().option() */
            String loop = dostmt.getText();
            PGTransition<String, String> exitdo = new PGTransition<>("","","","");
            for(NanoPromelaParser.OptionContext oc : dostmt.option()) {
                List<PGTransition<String, String>> subTransToAdd;
                subTransToAdd = generateTransitionsFromStatements(oc.stmt(), true);
                for(PGTransition<String, String> pgTrans : subTransToAdd) {
                    if(ifStatementHappend) {
                        if(!isNone(pgTrans.getFrom()))
                            pgTrans.setFrom(concatenate(pgTrans.getFrom(), loop));
                    } else {
                        if(isNone(pgTrans.getFrom()))
                            pgTrans.setFrom(loop);
                        else
                            pgTrans.setFrom(concatenate(pgTrans.getFrom(), loop));
                    }
                    if(pgTrans.getFrom().equals(loop) || isNone(pgTrans.getFrom())) {
                        if(isNone(pgTrans.getCondition()))
                            pgTrans.setCondition(parenthesis(oc.boolexpr().getText()));
                        else
                            pgTrans.setCondition(and(parenthesis(oc.boolexpr().getText()), parenthesis(pgTrans.getCondition())));
                    }

                    if(isNone(pgTrans.getTo()))
                        pgTrans.setTo(loop);
                    else
                        pgTrans.setTo(concatenate(pgTrans.getTo(),loop));
                }

                if(isNone(exitdo.getCondition()))
                    exitdo.setCondition(parenthesis(oc.boolexpr().getText()));
                else
                    exitdo.setCondition(or(exitdo.getCondition(), parenthesis(oc.boolexpr().getText())));

                resultTransitions.addAll(subTransToAdd);
                for(PGTransition<String, String> pgTrans : subTransToAdd) {
                    if(isNone(pgTrans.getFrom())) {
                        PGTransition<String, String> newPGT = new PGTransition<>(loop,pgTrans.getCondition(),pgTrans.getAction(),pgTrans.getTo());
                        resultTransitions.add(newPGT);
                    }
                }
            }

            exitdo.setCondition(not(parenthesis(exitdo.getCondition())));
            if(ifStatementHappend)
                resultTransitions.add(exitdo);

            PGTransition<String, String> exitdo2 = new PGTransition<>(loop,exitdo.getCondition(),"","");
            resultTransitions.add(exitdo2);
            return resultTransitions;
        }
        //endregion
        //region list of statements
        List<StmtContext> stmts;
        if((stmts = root.stmt())!= null){
            /* The sub-statements are the union of locations of the form[;root.stmt(1)] where is a sub-statement ofroot.stmt(0)and of all the sub-statements of root.stmt(1)*/
            String stmt2 = stmts.get(1).getText();
            List<PGTransition<String, String>> subStmtTrans1 = generateTransitionsFromStatements(stmts.get(0), ifStatementHappend);
            for(PGTransition<String, String> trans : subStmtTrans1){
                if(!ifStatementHappend || !isNone(trans.getFrom()))
                    trans.setFrom(concatenate(trans.getFrom(), stmt2));

                if(isNone(trans.getTo())){
                    trans.setTo(stmt2);
                }
                else trans.setTo(concatenate(trans.getTo(), stmt2));
            }

            resultTransitions.addAll(subStmtTrans1);
            List<PGTransition<String, String>> subStmtTrans2 = generateTransitionsFromStatements(stmts.get(1), false);
            resultTransitions.addAll(subStmtTrans2);
            return resultTransitions;
        }
        //endregion
        return resultTransitions;
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> p = product(ts, aut);
        for (Pair<S, Saut> state : p.getStates())
            for (Saut label : p.getLabel(state))
                if (aut.getAcceptingStates().contains(label) && isInCycle(p, state))
                    return verificationFailed(p, state);
        return new VerificationSucceeded<>();
    }

    private <S, Saut> VerificationResult<S> verificationFailed(TransitionSystem<Pair<S, Saut>, ?, Saut> p, Pair<S, Saut> state) {
        VerificationFailed<S> fail = new VerificationFailed<>();
        fail.setCycle(getFirsts(getStateCycle(p, state)));
        fail.setPrefix(getFirsts(getStatePrefix(p, state)));
        return fail;
    }

    private <S> boolean isInCycle(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> reachable = new HashSet<>();
        Set<S> expanded = new HashSet<>(post(ts, s));
        while (!reachable.equals(expanded)) expanded.addAll(post(ts, (reachable = new HashSet<>(expanded))));
        return reachable.contains(s);
    }

    private <S> List<S> getStateCycle(TransitionSystem<S, ?, ?> ts, S s) {
        List<List<S>> paths = new ArrayList<>();
        paths.add(Collections.singletonList(s));
        return getStatePaths(ts, s, paths, new HashSet<>());
    }

    private <S> List<S> getStatePrefix(TransitionSystem<S, ?, ?> ts, S s) {
        List<List<S>> paths = new ArrayList<>();
        ts.getInitialStates().forEach(state -> paths.add(Collections.singletonList(state)));
        return getStatePaths(ts, s, paths, new HashSet<>(ts.getInitialStates()));
    }

    private <S> List<S> getStatePaths(TransitionSystem<S, ?, ?> ts, S s, List<List<S>> paths, Set<S> visited) {
        List<S> ans = null;
        while (!visited.contains(s) && !paths.isEmpty()) {
            List<S> path = paths.remove(0);
            for (S state : post(ts, path.get(path.size() - 1))) {
                if (!visited.add(state)) continue;
                if (!s.equals(state)) {
                    List<S> temp = new ArrayList<>(path);
                    temp.add(state);
                    paths.add(temp);
                } else ans = path;
            }
        }
        return ans;
    }

    private <S, Saut> List<S> getFirsts(List<Pair<S, Saut>> list) {
        List<S> res = new ArrayList<>();
        list.forEach(p -> res.add(p.first));
        return res;
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
