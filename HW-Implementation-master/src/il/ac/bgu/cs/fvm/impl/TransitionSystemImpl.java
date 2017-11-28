package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.*;

public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {
    private String name;
    private Set<STATE> states;
    private Set<STATE> initialStates;
    private Set<ACTION> actions;
    private Set<ATOMIC_PROPOSITION> aps;
    private Set<Transition<STATE, ACTION>> transitions;

    private HashMap<STATE, Set<ATOMIC_PROPOSITION>> statesToLabels;

    public TransitionSystemImpl() {
        this.name = null;
        this.states = new HashSet<>();
        this.initialStates = new HashSet<>();
        this.actions = new HashSet<>();
        this.aps = new HashSet<>();
        this.transitions = new HashSet<>();
        this.statesToLabels = new HashMap<>();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TransitionSystemImpl<?, ?, ?> that = (TransitionSystemImpl<?, ?, ?>) o;

        if (name != null ? !name.equals(that.name) : that.name != null) return false;
        if (states != null ? !states.equals(that.states) : that.states != null) return false;
        if (initialStates != null ? !initialStates.equals(that.initialStates) : that.initialStates != null)
            return false;
        if (actions != null ? !actions.equals(that.actions) : that.actions != null) return false;
        if (aps != null ? !aps.equals(that.aps) : that.aps != null) return false;
        if (transitions != null ? !transitions.equals(that.transitions) : that.transitions != null) return false;
        return statesToLabels != null ? statesToLabels.equals(that.statesToLabels) : that.statesToLabels == null;
    }

    @Override
    public int hashCode() {
        int result = name != null ? name.hashCode() : 0;
        result = 31 * result + (states != null ? states.hashCode() : 0);
        result = 31 * result + (initialStates != null ? initialStates.hashCode() : 0);
        result = 31 * result + (actions != null ? actions.hashCode() : 0);
        result = 31 * result + (aps != null ? aps.hashCode() : 0);
        result = 31 * result + (transitions != null ? transitions.hashCode() : 0);
        result = 31 * result + (statesToLabels != null ? statesToLabels.hashCode() : 0);
        return result;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(ACTION action) {
        this.actions.add(action);
    }

    @Override
    public void addInitialState(STATE state) throws FVMException {
        if (!this.states.contains(state)) {
            throw new InvalidInitialStateException(state);
        }
        else initialStates.add(state);
    }

    @Override
    public void addState(STATE state) {
        this.states.add(state);
        this.statesToLabels.put(state, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        if (!states.contains(t.getFrom()) || !states.contains(t.getTo()) || !actions.contains(t.getAction())) {
            throw new InvalidTransitionException(t);
        }
        else this.transitions.add(t);
    }

    @Override
    public Set<ACTION> getActions() {
        return this.actions;
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        this.aps.add(p);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return this.aps;
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        if (!this.aps.contains(l)) {
            throw new InvalidLablingPairException(s, l);
        }
        else this.statesToLabels.get(s).add(l);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        if (!states.contains(s))
            throw new StateNotFoundException(String.format("state %s not found (getLabel)", s));

        return this.statesToLabels.get(s);
    }

    @Override
    public Set<STATE> getInitialStates() {
        return this.initialStates;
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return this.statesToLabels;
    }

    @Override
    public Set<STATE> getStates() {
        return this.states;
    }

    @Override
    public Set<Transition<STATE, ACTION>> getTransitions() {
        return this.transitions;
    }

    @Override
    public void removeAction(ACTION action) throws FVMException {
        for (Transition t : transitions)
            if (t.getAction().equals(action))
                throw new DeletionOfAttachedActionException(action, TransitionSystemPart.TRANSITIONS);
        this.actions.remove(action);
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        for (STATE s : this.states)
            if (statesToLabels.get(s).contains(p))
                throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.ATOMIC_PROPOSITIONS);
        this.aps.remove(p);
    }

    @Override
    public void removeInitialState(STATE state) {
        this.initialStates.remove(state);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        this.statesToLabels.get(s).remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        if (initialStates.contains(state))
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.INITIAL_STATES);

        if (!statesToLabels.get(state).isEmpty())
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);

        for (Transition t : transitions) {
            if (t.getTo().equals(state) || t.getFrom().equals(state))
                throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
        }
        this.states.remove(state);
    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        this.transitions.remove(t);
    }


}
