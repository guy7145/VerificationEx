package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.List;
import java.util.Set;

public class ProgramGraphImpl implements ProgramGraph {
    private String name;
    public ProgramGraphImpl() {
        this.name = null;
    }

    @Override
    public void addInitalization(List init) {

    }

    @Override
    public void addInitialLocation(Object location) {

    }

    @Override
    public void addLocation(Object o) {

    }

    @Override
    public void addTransition(PGTransition t) {

    }

    @Override
    public Set<List<String>> getInitalizations() {
        return null;
    }

    @Override
    public Set getInitialLocations() {
        return null;
    }

    @Override
    public Set getLocations() {
        return null;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public Set<PGTransition> getTransitions() {
        return null;
    }

    @Override
    public void removeLocation(Object o) {

    }

    @Override
    public void removeTransition(PGTransition t) {

    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
