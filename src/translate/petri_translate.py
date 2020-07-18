#! /usr/bin/env python3


import timers
import signal
import pddl
import normalize
import instantiate
from pddl.actions import PropositionalAction
from pddl.conditions import Atom, Condition
from pddl.effects import Effect
from pddl.tasks import Task
from petri.petri import PetriNet, PetriPlace, PetriTransition
from copy import deepcopy
from collections import defaultdict
import os
import sys
import traceback
from itertools import chain, combinations, product
from typing import Dict, Iterable, List, Tuple


def python_version_supported():
    return sys.version_info >= (3, 6)


if not python_version_supported():
    sys.exit("Error: Petri translator only supports Python >= 3.6.")

DEBUG = False


# For a full list of exit codes, please see driver/returncodes.py. Here,
# we only list codes that are used by the translator component of the planner.
PETRI_TRANSLATE_OUT_OF_MEMORY = 25
PETRI_TRANSLATE_OUT_OF_TIME = 26

simplified_effect_condition_counter = 0
added_implied_precondition_counter = 0


def powerset(iterable: Iterable) -> Iterable:
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)  # allows duplicate elements
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


def not_negated_effect(eff: Effect, preconditions: Condition) -> bool:
    """Return True if the effect don't negate any precondition.

    Args:
        eff (Effect): The effect.
        preconditions (Condition): All preconditions parts.

    Returns:
        bool: True if the effect don't negate any precondition and False otherwise.
    """
    # At the momemnt assume that the condition is a conjunction. TODO: more cases.
    # Assume that the effect is a Atom, the same for conditions parts
    negated_effect = eff.negate()
    for cond in preconditions:
        if cond.parts:
            parts = cond.parts
        else:
            parts = [cond]
        for part in parts:
            # If the effect is also a precondition (rare case), return False,
            # since it is not really an effect
            if part == negated_effect or part == eff:
                return False
    return True


def preconditions_atoms(preconditions: Condition) -> List[Atom]:
    """Return the preconditions that don't appear in effects or are negated in effects.

    Args:
        preconditions (Condition): All preconditions.

    Returns:
        List[Atom]: The preconditions atoms.
    """
    precond_atoms = []
    for cond in preconditions:
        if cond.parts:
            parts = cond.parts
        else:
            parts = [cond]
        for part in parts:
            precond_atoms.append(part)

    return precond_atoms


def join_add_del_effects(add_effects: List[Tuple[Condition, Effect]],
                         del_effects: List[Tuple[Condition, Effect]]) -> List[Effect]:
    """Join the add effects with the negated del effects to get all effects.

    Args:
        add_effects (List[Tuple[Condition, Effect]]): The add effects.
        del_effects (List[Tuple[Condition, Effect]]): The del effects.

    Returns:
        List[Effect]: The joined effects.
    """
    return [add[1] for add in add_effects] + [dele[1].negate() for dele in del_effects]


def equivalent_atom(atom: Atom, additional_literals: Dict[Atom, Atom]) -> Atom:
    """Return the equivalent atom (not_atom) if original and the atom without not else.

    Args:
        atom (Atom): The atom which equivalent is requested.
        additional_literals (Dict[Atom, Atom]): A relation of the
            original atoms with the new opposite ones.

    Returns:
        Atom: The equivalent atom (or None if not found).
    """
    for key, value in additional_literals.items():
        # the original atoms are negated
        if key.negate() == atom:
            return additional_literals[key]
        if value == atom:
            return key.negate()

    return None


def get_safe_operators(operators: List[PropositionalAction]) -> List[PropositionalAction]:
    """Get the 1-safe operators from the instantiated PropositionalActions.

    Args:
        operators (List[PropositionalAction]): The instantiated PropositionalActions.

    Returns:
        List[PropositionalAction]: The 1-safe operators.
    """
    safe_operators = []
    for op in operators:
        not_negated_effects = []
        # At the momemnt assume that the condition is a conjunction. TODO: more cases.
        preconditions = op.precondition
        # effects are separated in ADD and DEL, join them, condition of effects is ignored
        effects = join_add_del_effects(op.add_effects, op.del_effects)
        # search the effects no negated in the preconditions
        for eff in effects:
            if not_negated_effect(eff, preconditions):
                not_negated_effects.append(eff)
        negated_effects = set(effects).difference(set(not_negated_effects))
        if not not_negated_effects:
            safe_operators.append(op)
        else:
            # preconditions that are negated in effects or don't appear in effects
            orig_pre = set(preconditions_atoms(preconditions))
            for i, eprime in enumerate(powerset(not_negated_effects), 1):
                e = negated_effects.union(set(eprime))
                p = deepcopy(orig_pre)
                for not_negated in not_negated_effects:
                    if not_negated in e:
                        p.add(not_negated.negate())
                    else:
                        p.add(not_negated)
                safe_operators.append(PropositionalAction(
                    f"{op.name}_{i}", p, [([], eff) for eff in e], op.cost))
    return safe_operators


def remove_negative_preconditions(safe_operators: List[PropositionalAction]) -> Dict[Atom, Atom]:
    """Remove the negative preconditions of the safe operators creating new atoms.

    Args:
        safe_operators (List[PropositionalAction]): The safe operators.

    Returns:
        Dict[Atom, Atom]: The created atoms.

    Note:
        This function modifies the safe operators.
    """
    additional_literals = {}
    for n, op in enumerate(safe_operators):
        negated_preconds = []
        # a list is needed to get conditions in order
        preconds = list(op.precondition)
        for i, precond in enumerate(preconds):
            if precond.negated:
                not_precond = deepcopy(precond.negate())
                not_precond.predicate = f'not_{precond.predicate}'
                additional_literals[precond] = not_precond
                negated_preconds.append(i)
        # replace the negated preconditions with the new variable associated to it
        for i in negated_preconds:
            preconds[i] = additional_literals[preconds[i]]
        op.precondition = preconds
        # add the negated opposite literal for each effect
        effects = join_add_del_effects(op.add_effects, op.del_effects)
        new_effects = []
        for eff in effects:
            not_eff = deepcopy(eff.negate())
            not_eff.predicate = f'not_{eff.predicate}'
            if eff.negated:
                additional_literals[eff] = not_eff
            new_effects.append(not_eff)
        safe_operators[n] = PropositionalAction(
            op.name, op.precondition, [([], eff) for eff in effects + new_effects], op.cost)

    return additional_literals


def petri_mapping(atoms: List[Atom],
                  additional_literals: Dict[Atom, Atom],
                  safe_operators: List[PropositionalAction],
                  init: List[Atom]) -> PetriNet:
    """Map a set of safe operators, original atoms, new opposite atoms from
    original ones and the initial state to a Petri net using the Hickmott et al.
    mapping.

    Args:
        atoms (List[Atom]): The original instantiated atoms.
        additional_literals (Dict[Atom, Atom]): A relation of the
            original atoms with the new opposite ones.
        safe_operators (List[PropositionalAction]): The 1-safe operators.
        init (List[Atom]): the atoms in the initial state.

    Returns:
        PetriNet: The Petri net result of the mapping.
    """
    # remove all it is not Atom from init
    clean_init = set()
    for ini in init:
        if isinstance(ini, Atom):
            clean_init.add(ini)
    petri = PetriNet()
    # places are original atoms union opposite added ones, the initial marking
    # is 1 for original in init and 1 for correspondent opposite original not in init
    places = {}
    for atom in atoms:
        place = PetriPlace(str(atom))
        if atom in clean_init:
            place.add_token()
        petri.add_place(place)
        places[atom] = place
    for orig, added in additional_literals.items():
        place = PetriPlace(str(added))
        if orig.positive() not in clean_init:
            place.add_token()
        petri.add_place(place)
        places[added] = place

    for op in safe_operators:
        origins = []
        destinations = []
        # all preconditions go to origins, not read-only arc
        for precond in op.precondition:
            origins.append(precond)
        # all effects go to destinations
        # (the first element of the tuple is the condtion, ignored)
        for eff in op.add_effects:
            destinations.append(eff[1])
        # preconditions not negated in the effects go to destinations
        del_effects = [str(dele[1]) for dele in op.del_effects]
        for precond in op.precondition:
            str_dests = [str(dest) for dest in destinations]
            if str(precond) not in str_dests and str(precond) not in del_effects:
                destinations.append(precond)
        # get the PetriPlaces associated to the atoms
        origins = [places[orig] for orig in origins]
        destinations = [places[dest] for dest in destinations]
        petri.add_transition(PetriTransition(
            op.name, origins, destinations, op.cost))

    return petri


def pddl2petri(task: Task) -> PetriNet:
    """Convert a parsed PDDL into a Petri net using the Hickmott et al. method.

    Args:
        task (Task): The parsed PDDL.

    Returns:
        PetriNet: The Petri net obtained from the PDDL representation.
    """
    import translate
    relaxed_reachable, atoms, actions, axioms, _ = instantiate.explore(
        task)
    if not relaxed_reachable:
        return translate.unsolvable_sas_task("No relaxed solution")
    # 1. Convert the operators into 2^|e\¬p| safe operators
    safe_operators = get_safe_operators(actions)

    # 2. Remove negative preconditions
    additional_literals = remove_negative_preconditions(safe_operators)

    # 3. Map into Petri Net
    # places are state variables plus the opposite created
    # transitions are the safe operators, with arcs from precondictions to effects
    # the initial marking is a token in each initial state true and a token in each
    # opposite state where the original state is false
    return petri_mapping(atoms, additional_literals, safe_operators, task.init)


def main():
    # These imports are here instead of in top because the options import cause
    # that importing the file need domain and problem arguments, what is bad
    # for unit tests
    import options
    import pddl_parser
    timer = timers.Timer()
    with timers.timing("Parsing", True):
        task = pddl_parser.open(
            domain_filename=options.domain, task_filename=options.task)

    with timers.timing("Normalizing task"):
        normalize.normalize(task)

    petri = pddl2petri(task)

    with timers.timing("Writing output"):
        with open(options.sas_file, "w") as output_file:
            petri.sas_translate(task.goal, output_file)
    print("Done! %s" % timer)


def handle_sigxcpu(signum, stackframe):
    print()
    print("Translator hit the time limit")
    # sys.exit() is not safe to be called from within signal handlers, but
    # os._exit() is.
    os._exit(PETRI_TRANSLATE_OUT_OF_TIME)


if __name__ == "__main__":
    try:
        signal.signal(signal.SIGXCPU, handle_sigxcpu)
    except AttributeError:
        print("Warning! SIGXCPU is not available on your platform. "
              "This means that the planner cannot be gracefully terminated "
              "when using a time limit, which, however, is probably "
              "supported on your platform anyway.")
    try:
        # Reserve about 10 MB of emergency memory.
        # https://stackoverflow.com/questions/19469608/
        emergency_memory = b"x" * 10**7
        main()
    except MemoryError:
        del emergency_memory
        print()
        print("Translator ran out of memory, traceback:")
        print("=" * 79)
        traceback.print_exc(file=sys.stdout)
        print("=" * 79)
        sys.exit(PETRI_TRANSLATE_OUT_OF_MEMORY)
