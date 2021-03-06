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

package omega_automaton.acceptance;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jhoafparser.ast.AtomAcceptance;
import jhoafparser.ast.BooleanExpression;
import omega_automaton.AutomatonState;
import omega_automaton.collections.TranSet;
import omega_automaton.collections.Tuple;
import omega_automaton.collections.valuationset.ValuationSet;
import omega_automaton.output.HOAConsumerExtended;

public class GeneralisedRabinAcceptance<S extends AutomatonState<?>> implements OmegaAcceptance {

    protected final IdentityHashMap<TranSet<S>, Integer> acceptanceNumbers;
    protected final List<Tuple<TranSet<S>, List<TranSet<S>>>> acceptanceCondition;

    public GeneralisedRabinAcceptance(List<Tuple<TranSet<S>, List<TranSet<S>>>> acceptanceCondition) {
        this.acceptanceCondition = acceptanceCondition;
        for (int j = 0; j < this.acceptanceCondition.size(); j++) {
            Tuple<TranSet<S>, List<TranSet<S>>> pair = this.acceptanceCondition.get(j);
            for (int i = 0; i < pair.right.size(); i++) {
                pair.right.set(i, pair.right.get(i).copy());
            }
            this.acceptanceCondition.set(j, new Tuple<>(pair.left.copy(), pair.right));
        }
        this.acceptanceNumbers = new IdentityHashMap<>();
    }

    /**
     * Used by Prism
     */
    public List<Tuple<TranSet<S>, List<TranSet<S>>>> unmodifiableCopyOfAcceptanceCondition() {
        return Collections.unmodifiableList(acceptanceCondition);
    }

    public void addPair(Tuple<TranSet<S>, List<TranSet<S>>> tuple) {
        acceptanceCondition.add(tuple);
    }

    @Override
    public String getName() {
        return "generalized-Rabin";
    }

    @Override
    public List<Object> getNameExtra() {
        List<Object> extra = new ArrayList<>(acceptanceCondition.size() + 1);
        extra.add(acceptanceCondition.size());

        for (Tuple<TranSet<S>, List<TranSet<S>>> pair : acceptanceCondition) {
            extra.add(pair.right.size());
        }

        return extra;
    }

    @Override
    public int getAcceptanceSets() {
        int result = 0;
        for (Tuple<TranSet<S>, List<TranSet<S>>> pair : acceptanceCondition) {
            result += 1;
            result += pair.right.size();
        }
        return result;
    }

    protected int getTranSetId(TranSet<S> key) {
        acceptanceNumbers.putIfAbsent(key, acceptanceNumbers.keySet().size());
        return acceptanceNumbers.get(key);
    }

    @Override
    public BooleanExpression<AtomAcceptance> getBooleanExpression() {
        BooleanExpression<AtomAcceptance> disjunction = null;

        for (int offset = 0; offset < acceptanceCondition.size(); offset++) {
            Tuple<TranSet<S>, List<TranSet<S>>> pair = acceptanceCondition.get(offset);
            BooleanExpression<AtomAcceptance> conjunction = HOAConsumerExtended.mkFin(getTranSetId(pair.left));

            conjunction = addInfiniteSetsToConjunction(conjunction, offset);

            if (disjunction == null) {
                disjunction = conjunction;
            } else {
                disjunction = disjunction.or(conjunction);
            }
        }

        return (disjunction != null ? disjunction : new BooleanExpression<>(false));
    }

    // to be overriden by GeneralisedRabinWithMeanPayoffAcceptance
    protected BooleanExpression<AtomAcceptance> addInfiniteSetsToConjunction(BooleanExpression<AtomAcceptance> conjunction, int offset) {
        Tuple<TranSet<S>, List<TranSet<S>>> pair = acceptanceCondition.get(offset);
        for (TranSet<S> inf : pair.right) {
            conjunction = conjunction.and(HOAConsumerExtended.mkInf(getTranSetId(inf)));
        }
        return conjunction;
    }

    public Set<ValuationSet> getMaximallyMergedEdgesOfEdge(AutomatonState<?> currentState, ValuationSet initialValuation) {
        Set<ValuationSet> result = new HashSet<>();
        result.add(initialValuation);

        for (TranSet<S> acceptanceCondition : acceptanceNumbers.keySet()) {
            result = splitAccordingToAcceptanceSet(currentState, result, acceptanceCondition);
        }

        return result;
    }

    protected Set<ValuationSet> splitAccordingToAcceptanceSet(AutomatonState<?> currentState, Set<ValuationSet> result, TranSet<S> acceptanceCondition) {
        Set<ValuationSet> toRemove = new HashSet<>();
        Set<ValuationSet> toAdd = new HashSet<>();

        for (ValuationSet edge : result) {
            ValuationSet interestingValuationSet = acceptanceCondition.asMap().get(currentState);
            if (interestingValuationSet != null && interestingValuationSet.intersects(edge) && !interestingValuationSet.containsAll(edge)) {
                toRemove.add(edge);
                toAdd.add(edge.intersect(interestingValuationSet));
                toAdd.add(edge.intersect(interestingValuationSet.complement()));
            }
        }

        result.removeAll(toRemove);
        result.addAll(toAdd);
        return result;
    }

    public List<Integer> getInvolvedAcceptanceNumbers(AutomatonState<?> currentState, ValuationSet edgeKey) {
        List<Integer> result = new ArrayList<>();
        acceptanceNumbers.keySet().stream().filter(set -> set.containsAll(currentState, edgeKey)).forEach(set -> result.add(acceptanceNumbers.get(set)));
        return result;
    }

    /**
     * checks if premise implies conclusion (as acceptance pair)
     */
    public boolean implies(int premiseIndex, int conclusionIndex) {
        Tuple<TranSet<S>, List<TranSet<S>>> premise = acceptanceCondition.get(premiseIndex);
        Tuple<TranSet<S>, List<TranSet<S>>> conclusion = acceptanceCondition.get(conclusionIndex);
        return premise.left.containsAll(conclusion.left) && conclusion.right.stream().allMatch(inf2 -> premise.right.stream().anyMatch(inf2::containsAll));
    }

    /**
     * This method is important if an Acceptance has something to say, which is
     * not supported for HOA-format. To be overriden by subclasses
     */
    public Map<String, List<Object>> miscellaneousAnnotations() {
        return Collections.emptyMap();
    }

    public void removeIndices(Set<Integer> toRemove) {
        toRemove.stream().sorted(Collections.reverseOrder()).forEachOrdered(index -> acceptanceCondition.remove(index.intValue()));
    }

    public void addEach(Collection<Tuple<TranSet<S>, List<TranSet<S>>>> temp) {
        acceptanceCondition.addAll(temp);
    }

    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("GeneralisedRabinAcceptance\n");
        for (int i = 0; i < acceptanceCondition.size(); i++) {
            builder.append("\nPair ");
            builder.append(i);
            builder.append('\n');
            builder.append('\t');
            builder.append("Fin: ");
            builder.append(acceptanceCondition.get(i).left);
            for (int j = 0; j < acceptanceCondition.get(i).right.size(); j++) {
                builder.append("\n\tInf: ");
                builder.append(j);
                builder.append(": ");
                builder.append(acceptanceCondition.get(i).right.get(j));
            }
        }
        return builder.toString();
    }

    public void removeEach() {
        acceptanceCondition.clear();
    }
}
