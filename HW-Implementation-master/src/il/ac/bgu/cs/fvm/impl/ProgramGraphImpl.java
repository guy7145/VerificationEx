package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {
    private String name;
    private Set<L> locations;
    private Set<L> initialLocations;
    private Set<List<String>> initializations;
    private Set<PGTransition<L, A>> transitions;

    public ProgramGraphImpl() {
        this.name = null;
        this.locations = new HashSet<>();
        this.initialLocations = new HashSet<>();
        this.initializations = new HashSet<>();
        this.transitions = new HashSet<>();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProgramGraphImpl<?, ?> that = (ProgramGraphImpl<?, ?>) o;

        if (name != null ? !name.equals(that.name) : that.name != null) return false;
        if (locations != null ? !locations.equals(that.locations) : that.locations != null) return false;
        if (initialLocations != null ? !initialLocations.equals(that.initialLocations) : that.initialLocations != null)
            return false;
        if (initializations != null ? !initializations.equals(that.initializations) : that.initializations != null)
            return false;
        return transitions != null ? transitions.equals(that.transitions) : that.transitions == null;
    }

    @Override
    public int hashCode() {
        int result = name != null ? name.hashCode() : 0;
        result = 31 * result + (locations != null ? locations.hashCode() : 0);
        result = 31 * result + (initialLocations != null ? initialLocations.hashCode() : 0);
        result = 31 * result + (initializations != null ? initializations.hashCode() : 0);
        result = 31 * result + (transitions != null ? transitions.hashCode() : 0);
        return result;
    }

    @Override
    public void addInitalization(List<String> init) {
        this.initializations.add(init);
    }

    @Override
    public void addInitialLocation(L location) {
        this.initialLocations.add(location);
    }

    @Override
    public void addLocation(L l) {
        this.locations.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        this.transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return this.initializations;
    }

    @Override
    public Set<L> getInitialLocations() {
        return this.initialLocations;
    }

    @Override
    public Set<L> getLocations() {
        return this.locations;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return this.transitions;
    }

    @Override
    public void removeLocation(L l) {
        this.locations.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        this.transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
