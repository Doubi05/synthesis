import molehill
import payntbind
import math
from molehill.mole import Mole
from molehill.constraints import ExistsForallConstraint
from molehill.constraints import DecisionTree
from types import SimpleNamespace
from argparse import Namespace
import z3
import argparse
import json


def run_molehill_for_game_abstraction(quotient, decision_tree_nodes=0):
    if decision_tree_nodes > 0:
        #looking for a robust policy in the form of a decision tree
        constraint = DecisionTree(robust=True)
        constraint.set_args(Namespace(forall="sketch_hole", random=False, nodes=decision_tree_nodes, pictures=None))
    else:
        #looking for a robust policy in a tabular form
        constraint = ExistsForallConstraint()
        constraint.set_args(Namespace(forall="sketch_hole", random=False))
    
    # add holes for the universally quantified variables
    quotient.family.hole_to_name = [
            "sketch_hole_" + x for x in quotient.family.hole_to_name
        ]
    
    choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
    family = quotient.family
    def _get_state_valuations(model):
        """Identify variable names and extract state valuation in the same order."""
        assert model.has_state_valuations(), "model has no state valuations"
        # get name
        sv = model.state_valuations
        variable_name = None
        state_valuations = []
        for state in range(model.nr_states):
            valuation = json.loads(str(sv.get_json(state)))
            if variable_name is None:
                variable_name = list(valuation.keys())
            valuation = [valuation[var_name] for var_name in variable_name]
            state_valuations.append(valuation)
        return variable_name, state_valuations
    var_names, state_valuations = _get_state_valuations(quotient.quotient_mdp)
    
    nci = quotient.quotient_mdp.nondeterministic_choice_indices.copy()
    
    # add holes for the existentially quantified variables (only those with multiple actions available)
    for state in range(quotient.quotient_mdp.nr_states):
        if (
            len(quotient.state_to_actions[state]) > 1
        ):  # again if there's only one action in a state there's no point in adding a hole
            option_labels = [
                quotient.action_labels[i]
                for i in quotient.state_to_actions[state]
            ]
            vals_here = "&".join(
                [
                    f"{var_name}={int(state_valuations[state][i])}"
                    for i, var_name in enumerate(var_names)
                    if not var_name.startswith("_loc_prism2jani")
                ]
            )
            hole_name = f"A([{vals_here}])"
            
            hole_index = quotient.family.num_holes
            quotient.family.add_hole(hole_name, option_labels)
                
            for choice in range(nci[state], nci[state + 1]):
                action_hole_index = quotient.state_to_actions[state].index(
                    quotient.choice_to_action[choice]
                )
                choice_to_hole_options[choice].append(
                    (hole_index, action_hole_index)
                )
                
    quotient.coloring = payntbind.synthesis.Coloring(
        family.family,
        quotient.quotient_mdp.nondeterministic_choice_indices,
        choice_to_hole_options,
    )
    family = quotient.family
    
    s = z3.Solver()
    constraint.solver_settings(s)
    # set solver timeout in milliseconds
    timeout_ms = 240000 # 4 minutes
    s.set("timeout", timeout_ms)
   
    variables = []
    variables_in_ranges = None
    num_bits = (
        max(
            [
                math.ceil(math.log2(len(family.hole_options(hole)) + 1))
                for hole in range(family.num_holes)
            ]
        )
        + 1
    )
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)

    def variables_in_ranges2(variables):
        statement = []
        for hole in range(family.num_holes):
            options = family.hole_options(hole)
            var = variables[hole]
            statement.append(z3.UGE(var, z3.BitVecVal(min(options), num_bits)))
            statement.append(z3.ULE(var, z3.BitVecVal(max(options), num_bits)))
        return z3.And(*statement)
    variables_in_ranges = variables_in_ranges2
    f = z3.PropagateFunction("valid", *[x.sort() for x in variables], z3.BoolSort())
    
    s.add(
        constraint.build_constraint(
            f, variables, variables_in_ranges, family=family, quotient=quotient
        )
    )  
    
    p = Mole(
        s,
        variables,
        quotient,
        considered_counterexamples="none",
    )
    
    check_result = s.check()  
    if check_result == z3.sat:
        # sat
        sat = True
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            if var.__str__().startswith("sketch_hole_"):
                continue
            if hasattr(model.eval(var), "as_long"):
                new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # re-check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        
        #convert the policy to list of action indices for the quotient MDP states
        label_to_int = {label: i for i, label in enumerate(quotient.action_labels)}
        chosen_actions = []
        holes_index = 0
        for state_index in range(0, len(quotient.state_to_actions)):
            if len(quotient.state_to_actions[state_index]) == 1:
                # only one action available for a state
                chosen_actions.append(quotient.state_to_actions[state_index][0])
            else:  
                # more actions available for a state   
                while new_family.hole_name(holes_index).startswith("sketch_hole_"):
                    # skip holes for universally quantified variables
                    holes_index += 1 
                    
                # Check the valuations in the hole name match the model's state valuations for this state
                vals_here = "&".join(
                    [
                        f"{var_name}={int(state_valuations[state_index][i])}"
                        for i, var_name in enumerate(var_names)
                        if not var_name.startswith("_loc_prism2jani")
                    ]
                )
                expected_hole_name = f"A([{vals_here}])"
                assert new_family.hole_name(holes_index) == expected_hole_name, f"Hole mismatch for state {state_index}: expected {expected_hole_name}, got {new_family.hole_name(holes_index)}"            
                
                # get the chosen option for this hole from the model and convert it to an action index
                option = new_family.hole_options(holes_index)[0]                 
                label = new_family.hole_to_option_labels[holes_index][option]   
                label_number = label_to_int[label]
                chosen_actions.append(label_number)
                holes_index += 1
                
    elif check_result == z3.unknown:
        # unknown result due to timeout, treat as unsat
        print("unknown, timeout")
        chosen_actions = None
        sat = False

    else:
        # unsat
        chosen_actions = None
        sat = False

    del s
    del variables
    del f
    z3.reset_params()
    return chosen_actions, sat