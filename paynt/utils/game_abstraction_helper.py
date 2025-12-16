import molehill
import payntbind
import math
from molehill.mole import Mole
from molehill.constraints import ExistsForallConstraint
from molehill.constraints import ExistsConstraint
from types import SimpleNamespace
import z3


def run_molehill_for_game_abstraction(quotient):
    constraint = ExistsForallConstraint()
    constraint.set_args(SimpleNamespace(forall="sketch_hole", random=False))
    
    quotient.family.hole_to_name = [
            "sketch_hole_" + x for x in quotient.family.hole_to_name
        ]  # feel free to change the prefix, this should just make it easier to creat exists forall queries
    
    choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
    family = quotient.family

    nci = quotient.quotient_mdp.nondeterministic_choice_indices.copy()
    for state in range(quotient.quotient_mdp.nr_states):
        if (
            len(quotient.state_to_actions[state]) > 1
        ):  # again if there's only one action in a state there's no point in adding a hole
            option_labels = [
                quotient.action_labels[i]
                for i in quotient.state_to_actions[state]
            ]
            hole_name = f"A(S{state//2},M{state%2})"
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

    #print(family)

    s = z3.Solver()
    constraint.solver_settings(s)
   
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
            # it gets guaranteed by paynt that this is actually the range
            # (these are just the indices, not the actual values in the final model :)
            assert min(options) == 0
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
    
    
    if s.check() == z3.sat:
        print("sat")
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            # if var has as_long attribute
            if hasattr(model.eval(var), "as_long"):
                new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # re-check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        print(f"Found {new_family} with value {result}")
    else:
        print("unsat")
    print("finished")
    exit()