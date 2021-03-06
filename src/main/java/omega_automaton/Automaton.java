/*
 * Copyright (C) 2016  (See AUTHORS)
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package omega_automaton;

import java.util.ArrayDeque;
import java.util.BitSet;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import javax.annotation.Nullable;

import com.google.common.collect.BiMap;

import jhoafparser.consumer.HOAConsumer;
import omega_automaton.acceptance.AllAcceptance;
import omega_automaton.acceptance.OmegaAcceptance;
import omega_automaton.collections.Collections3;
import omega_automaton.collections.valuationset.ValuationSet;
import omega_automaton.collections.valuationset.ValuationSetFactory;
import omega_automaton.output.HOAConsumerExtended;

public abstract class Automaton<S extends AutomatonState<S>, Acc extends OmegaAcceptance> {

    @Nullable
    protected S initialState;
    protected final Map<S, Map<Edge<S>, ValuationSet>> transitions;
    protected Acc acceptance;

    protected final ValuationSetFactory valuationSetFactory;

    protected Automaton(Acc acceptance, ValuationSetFactory factory) {
        transitions = new HashMap<>();
        valuationSetFactory = factory;
        this.acceptance = acceptance;
    }

    public void generate() {
        generate(getInitialState());
    }

    public void generate(@Nullable S initialState) {
        if (initialState == null) {
            return;
        }

        // Return if already generated
        if (transitions.containsKey(initialState)) {
            return;
        }

        Set<S> workSet = new HashSet<>();
        workSet.add(initialState);

        while (!workSet.isEmpty()) {
            S current = Collections3.removeElement(workSet);

            for (Edge<S> successor : getSuccessors(current).keySet()) {
                if (!transitions.containsKey(successor.successor)) {
                    workSet.add(successor.successor);
                }
            }
        }
    }

    public boolean hasSuccessors(S state) {
        return !getSuccessors(state).isEmpty();
    }

    public boolean isSink(S state) {
        for (Map.Entry<Edge<S>, ValuationSet> entry : getSuccessors(state).entrySet()) {
            if (!entry.getKey().successor.equals(state) && !entry.getValue().isEmpty()) {
                return false;
            }
        }

        return true;
    }

    public boolean isTransient(S state) {
        for (Map.Entry<Edge<S>, ValuationSet> entry : getSuccessors(state).entrySet()) {
            if (entry.getKey().successor.equals(state) && !entry.getValue().isEmpty()) {
                return false;
            }
        }

        return true;
    }

    public boolean isDeterministic() {
        return getStates().stream().allMatch(this::isDeterministic);
    }

    public boolean isDeterministic(S state) {
        ValuationSet valuationSet = valuationSetFactory.createEmptyValuationSet();

        for (Map.Entry<Edge<S>, ValuationSet> entry : getSuccessors(state).entrySet()) {
            if (valuationSet.intersects(entry.getValue())) {
                valuationSet.free();
                return false;
            } else {
                valuationSet.addAll(entry.getValue());
            }
        }

        valuationSet.free();
        return true;
    }

    @Nullable
    public Edge<S> getSuccessor(S state, BitSet valuation) {
        for (Map.Entry<Edge<S>, ValuationSet> transition : getSuccessors(state).entrySet()) {
            if (transition.getValue().contains(valuation)) {
                return transition.getKey();
            }
        }

        return null;
    }

    public Set<S> getSuccessors(S state, BitSet valuation) {
        Set<S> successors = new HashSet<>();

        for (Map.Entry<Edge<S>, ValuationSet> transition : getSuccessors(state).entrySet()) {
            if (transition.getValue().contains(valuation)) {
                successors.add(transition.getKey().successor);
            }
        }

        return successors;
    }

    public Map<Edge<S>, ValuationSet> getSuccessors(S state) {
        Map<Edge<S>, ValuationSet> row = transitions.get(state);

        if (row == null) {
            row = state.getSuccessors();
            transitions.put(state, row);
        }

        return row;
    }

    public int size() {
        return transitions.size();
    }

    public S getInitialState() {
        if (initialState == null) {
            initialState = generateInitialState();
        }

        return initialState;
    }

    public Set<S> getStates() {
        return new HashSet<>(transitions.keySet());
    }

    public void removeUnreachableStates() {
        Set<S> states = new HashSet<>();
        states.add(getInitialState());
        removeUnreachableStates(states);
    }

    public void removeUnreachableStates(Set<S> reach) {
        getReachableStates(reach);
        removeStatesIf(s -> !reach.contains(s));
    }

    /**
     * This method removes unused states and their in- and outgoing transitions.
     * If the set dependsOn the initial state, it becomes an automaton with the
     * only state false. Use this method only if you are really sure you want to
     * remove the states!
     *
     * @param states:
     *            Set of states that is to be removed
     */
    public void removeStates(Collection<S> states) {
        if (states.contains(initialState)) {
            initialState = null;
            transitions.clear();
        } else {
            removeStatesIf(states::contains);
        }
    }

    public void removeStatesIf(Predicate<S> predicate) {
        transitions.keySet().removeIf(predicate);
        transitions.forEach((k, v) -> v.keySet().removeIf(t -> predicate.test(t.successor)));

        if (predicate.test(initialState)) {
            initialState = null;
        }
    }

    public ValuationSetFactory getFactory() {
        return valuationSetFactory;
    }

    public Acc getAcceptance() {
        return acceptance;
    }

    @Nullable
    protected S generateInitialState() {
        return null;
    }

    /**
     * This method has no side effects
     *
     * @param scc:
     *            set of states
     * @return true if the only transitions from scc go to scc again and false
     *         otherwise
     */
    public boolean isBSCC(Set<S> scc) {
        for (S s : scc) {
            for (Edge<S> outgoingEdge : getSuccessors(s).keySet()) {
                if (!scc.contains(outgoingEdge.successor)) {
                    return false;
                }
            }
        }

        return true;
    }

    private void getReachableStates(Set<S> states) {
        Deque<S> workDeque = new ArrayDeque<>(states);

        while (!workDeque.isEmpty()) {
            S state = workDeque.remove();

            getSuccessors(state).forEach((suc, v) -> {
                if (states.add(suc.successor)) {
                    workDeque.add(suc.successor);
                }
            });
        }
    }

    public void toHOA(HOAConsumer ho, BiMap<String, Integer> aliases) {
        HOAConsumerExtended hoa = new HOAConsumerExtended(ho, valuationSetFactory, aliases, acceptance != null ? acceptance : new AllAcceptance(), initialState, size());
        toHOABody(hoa);
        hoa.done();
    }

    public void toHOABody(HOAConsumerExtended hoa) {
        for (S s : getStates()) {
            hoa.addState(s);
            toHOABodyEdge(s, hoa);
            hoa.stateDone();
        }
    }

    /**
     * Override this method, if you want output additional edges for
     * {@param state} not present in {@link Automaton#transitions}.
     *
     * @param state
     * @param hoa
     */
    protected void toHOABodyEdge(S state, HOAConsumerExtended hoa) {
        getSuccessors(state).forEach((k, v) -> hoa.addEdge(v, k.successor, k.acceptance));
    }

    public void free() {
        initialState = null;
        acceptance = null;

        transitions.forEach((k, v) -> {
            k.free();
            v.forEach((e, val) -> {
                e.successor.free();
                val.free();
            });
        });
    }
}
