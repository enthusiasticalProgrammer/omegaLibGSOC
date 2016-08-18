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

package omega_automaton.output;

import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import com.google.common.collect.BiMap;

import jhoafparser.ast.AtomAcceptance;
import jhoafparser.ast.AtomLabel;
import jhoafparser.ast.BooleanExpression;
import jhoafparser.consumer.HOAConsumer;
import jhoafparser.consumer.HOAConsumerException;
import omega_automaton.AutomatonState;
import omega_automaton.acceptance.GeneralisedRabinAcceptance;
import omega_automaton.acceptance.NoneAcceptance;
import omega_automaton.acceptance.OmegaAcceptance;
import omega_automaton.collections.Collections3;
import omega_automaton.collections.valuationset.ValuationSet;
import omega_automaton.collections.valuationset.ValuationSetFactory;

public class HOAConsumerExtended {

    protected static final Logger logger = Logger.getLogger(HOAConsumerExtended.class.getName());

    private final HOAConsumer hoa;
    private final Map<AutomatonState<?>, Integer> stateNumbers;
    protected AutomatonState<?> currentState;
    private final @Nullable BiMap<String, Integer> literalNames;

    public HOAConsumerExtended(HOAConsumer hoa, ValuationSetFactory valSetFac, @Nullable BiMap<String, Integer> aliases, @Nonnull OmegaAcceptance acceptance,
            AutomatonState<?> initialState, int size) {
        this.hoa = hoa;
        stateNumbers = new HashMap<>(size);
        literalNames = aliases;

        try {
            hoa.notifyHeaderStart("v1");

            hoa.setTool("Rabinizer Controller Synthesis", "1.0");
            hoa.setName("Automaton for " + ((initialState != null) ? initialState.toString() : "false"));

            if (size >= 0) {
                hoa.setNumberOfStates(size);
            }

            if (initialState != null && size > 0) {
                hoa.addStartStates(Collections.singletonList(getStateId(initialState)));
                if (acceptance.getName() != null) {
                    hoa.provideAcceptanceName(acceptance.getName(), acceptance.getNameExtra());
                }

                hoa.setAcceptanceCondition(acceptance.getAcceptanceSets(), acceptance.getBooleanExpression());
            } else {
                OmegaAcceptance acceptance1 = new NoneAcceptance();
                hoa.provideAcceptanceName(acceptance1.getName(), acceptance1.getNameExtra());
                hoa.setAcceptanceCondition(acceptance1.getAcceptanceSets(), acceptance1.getBooleanExpression());
            }

            if (literalNames == null) {
                hoa.setAPs(IntStream.range(0, valSetFac.getSize()).mapToObj(Integer::toString).collect(Collectors.toList()));
            } else {
                hoa.setAPs(IntStream.range(0, valSetFac.getSize()).mapToObj(i -> literalNames.inverse().get(i)).collect(Collectors.toList()));
                for (Entry<String, Integer> entry : literalNames.entrySet()) {
                    hoa.addAlias(entry.getKey(), new BooleanExpression<>(AtomLabel.createAPIndex(entry.getValue())));
                }
            }
            if (acceptance instanceof GeneralisedRabinAcceptance) {
                Map<String, List<Object>> map = ((GeneralisedRabinAcceptance<?>) acceptance).miscellaneousAnnotations();

                try {
                    for (Entry<String, List<Object>> entry : map.entrySet()) {
                        hoa.addMiscHeader(entry.getKey(), entry.getValue());
                    }
                } catch (HOAConsumerException ex) {
                    logger.warning(ex.toString());
                }
            }
            hoa.notifyBodyStart();

            if (initialState == null || size == 0) {
                hoa.notifyEnd();
            }
        } catch (HOAConsumerException ex) {
            logger.warning(ex.toString());
        }
    }

    public static BooleanExpression<AtomAcceptance> mkInf(int number) {
        return new BooleanExpression<>(new AtomAcceptance(AtomAcceptance.Type.TEMPORAL_INF, number, false));
    }

    public static BooleanExpression<AtomAcceptance> mkFin(int number) {
        return new BooleanExpression<>(new AtomAcceptance(AtomAcceptance.Type.TEMPORAL_FIN, number, false));
    }

    public void addState(AutomatonState<?> state) {
        try {
            currentState = state;
            hoa.addState(getStateId(state), state.toString(), null, null);
        } catch (HOAConsumerException ex) {
            logger.warning(ex.toString());
        }
    }

    public void stateDone() {
        try {
            hoa.notifyEndOfState(getStateId(currentState));
        } catch (HOAConsumerException ex) {
            logger.warning(ex.toString());
        }
    }

    public void done() {
        try {
            if (!stateNumbers.isEmpty()) {
                hoa.notifyEnd();
            }
        } catch (HOAConsumerException ex) {
            logger.warning(ex.toString());
        }
    }

    public void addEdge(ValuationSet key, AutomatonState<?> end) {
        addEdgeBackend(key, end, null);
    }

    public void addEdge(ValuationSet label, AutomatonState<?> end, BitSet accSets) {
        addEdgeBackend(label, end, Collections3.toList(accSets));
    }

    public void addEpsilonEdge(AutomatonState<?> successor) {
        try {
            System.err.print("Warning: HOA currently does not support epsilon-transitions. (" + currentState + " -> " + successor + ')');
            hoa.addEdgeWithLabel(getStateId(currentState), null, Collections.singletonList(getStateId(successor)), null);
        } catch (HOAConsumerException ex) {
            logger.warning(ex.toString());
        }
    }

    protected void addEdgeBackend(ValuationSet label, AutomatonState<?> end, List<Integer> accSets) {
        if (label.isEmpty()) {
            return;
        }

        try {
            hoa.addEdgeWithLabel(getStateId(currentState), label.toExpression(literalNames), Collections.singletonList(getStateId(end)), accSets);
        } catch (HOAConsumerException ex) {
            logger.warning(ex.toString());
        }
    }

    private int getStateId(AutomatonState<?> state) {
        stateNumbers.putIfAbsent(state, stateNumbers.size());
        int result = stateNumbers.get(state);
        return stateNumbers.get(state);
    }

}
