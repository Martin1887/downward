from petri_translate import get_safe_operators, \
    remove_negative_preconditions, petri_mapping
from pddl.actions import PropositionalAction
from pddl.conditions import Atom, Condition
from pddl.effects import Effect
from pddl.tasks import Task
from petri.petri import PetriNet, PetriPlace, PetriTransition


def test_hickmott_example():
    """Test that the translations of operator x = ({a, ¬b}, {¬a, d}) generates
    the Petri net specified in Hickmott et al. with safe operators
    x'1 = ({a, not_b, d}, {¬a, not_a}) and
    x'2 = ({a, not_b, not_d}, {not_a, ¬a, ¬not_d, d}).
    A initial state when only a is True is added to also check the initial
    mapping.

    Returns:
        bool: True if everything is right and False otherwise.
    """
    atoms = [Atom('a', []), Atom('b', []), Atom('d', [])]
    actions = [PropositionalAction('x', [Condition([Atom('a', [])]),
                                         Condition([Atom('b', []).negate()])],
                                   [([], Atom('a', []).negate()), ([], Atom('d', []))], 0)]
    init = [Atom('a', [])]

    for ac in actions:
        ac.dump()
    safe_operators = get_safe_operators(actions)
    print(f'safe_operators: {safe_operators}')
    for op in safe_operators:
        op.dump()
    additional_literals = remove_negative_preconditions(safe_operators)
    print(f'additional_literals: {additional_literals}')
    for op in safe_operators:
        op.dump()
    petri = petri_mapping(atoms, additional_literals,
                          safe_operators, init)
    print(petri)
    petri.dump()

    expected_petri = PetriNet()
    a = PetriPlace('Atom a()')
    a.add_token()
    b = PetriPlace('Atom b()')
    d = PetriPlace('Atom d()')
    not_a = PetriPlace('Atom not_a()')
    not_b = PetriPlace('Atom not_b()')
    not_b.add_token()
    not_d = PetriPlace('Atom not_d()')
    not_d.add_token()

    expected_petri.add_place(b)
    expected_petri.add_place(d)
    expected_petri.add_place(not_a)
    expected_petri.add_place(a)
    expected_petri.add_place(not_b)
    expected_petri.add_place(not_d)

    expected_petri.add_transition(PetriTransition("op1", [a, d, not_b],
                                                  [not_a, d, not_b], 0))
    expected_petri.add_transition(PetriTransition("op2", [a, not_b, not_d],
                                                  [not_a, d, not_b], 0))

    assert len(set(petri.places).symmetric_difference(
        set(expected_petri.places))) == 0

    if len(set(petri.transitions).symmetric_difference(
            set(expected_petri.transitions))) > 0:
        print('Petri transitions:')
        for tran in petri.transitions:
            print(tran)
        print('Excpected Petri transitions:')
        for tran in expected_petri.transitions:
            print(tran)
    assert len(set(petri.transitions).symmetric_difference(
        set(expected_petri.transitions))) == 0
    assert petri == expected_petri


if __name__ == '__main__':
    test_hickmott_example()
