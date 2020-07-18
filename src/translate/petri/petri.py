from typing import List, Tuple
import sas_tasks


class PetriPlace():
    """Place of a PetriNet object.
    """

    def __init__(self, name: str):
        """Constructor that names the place and initialize 0 tokens in it.

        Args:
            name (str): The naem for the place.
        """
        self.name = name
        self.tokens = 0

    def __hash__(self):
        return hash((self.__class__, self.name, self.tokens))

    def __eq__(self, other):
        return (self.name == other.name and self.tokens == other.tokens)

    def __ne__(self, other):
        return not self == other

    def __str__(self):
        return f'PetriPlace({self.name}, {self.tokens})'

    def __repr__(self):
        return str(self)

    def add_tokens(self, n_tokens: int):
        """Add `n_tokens` tokens to the place.

        Args:
            n_tokens (int): The number of tokens to add.
        """
        self.tokens += n_tokens

    def add_token(self):
        """Add 1 token to the place.
        """
        self.add_tokens(1)


class PetriTransition():
    """Transition of a PetriNet object.
    """

    def __init__(self, name: str, origins: List[PetriPlace], destinations: List[PetriPlace], cost: int):
        """Constructor with the list of origins and destinations.

        Args:
            name (str): The name of the operator.
            origins (List[PetriPlace]): List of destinations.
                The first field of the tuple is the place and the second one is the
                readonly property of the arc.
            destinations (List[PetriPlace]): List of destinations of the transitions.
            cost (int): The cost of the action.
        """
        self.name = name
        self.origins = origins
        self.destinations = destinations
        self.cost = cost

    def __hash__(self):
        return hash((self.__class__, tuple(sorted(set(self.origins), key=str)), tuple(sorted(set(self.destinations), key=str)), self.cost))

    def __eq__(self, other):
        return (len(set(self.origins).symmetric_difference(set(other.origins))) == 0 and
                len(set(self.destinations).symmetric_difference(set(other.destinations))) == 0 and
                self.cost == other.cost)

    def __ne__(self, other):
        return not self == other

    def __str__(self):
        return f'PetriTransition({[str(orig) for orig in self.origins]}, {[str(dest) for dest in self.destinations]}, {self.cost})'


class PetriNet():
    """Petri net with places and transitions. Arcs from places to transitions can
    be readonly.
    """

    def __init__(self):
        """Constructor with places and transitions empty.
        """
        self.places = []
        self.transitions = []

    def __hash__(self):
        return hash((self.__class__, tuple(self.places), tuple(self.transitions)))

    def __eq__(self, other):
        return (len(set(self.places).symmetric_difference(other.places)) == 0 and
                len(set(self.transitions).symmetric_difference(other.transitions)) == 0)

    def __ne__(self, other):
        return not self == other

    def __str__(self):
        return f'Petri({self.places}, {self.transitions})'

    def add_place(self, place: PetriPlace):
        """Add a place to the Petri net.

        Args:
            place (PetriPlace): The place to add.
        """
        self.places.append(place)

    def add_transition(self, transition: PetriTransition):
        """Add a transition to the Petri net

        Args:
            transition (PetriTransition): The transition to add.
        """
        self.transitions.append(transition)

    def dump(self):
        """Print a description of the Petri net.
        """
        print('Places:')
        for place in self.places:
            print(f'{place.name}, {place.tokens}')
        print('Transitions:')
        for tran in self.transitions:
            print(f'Origins: {tran.origins}')
            print(f'Destinations: {tran.destinations}')

    def sas_translate(self, goal, output):
        """Map the Petri net into a SAS translation representation, that
        can be written into a file.

        Args:
            goal: The PDDL task goal.
            output: A stream where write the translation.
        """
        ranges = []
        axiom_layers = []
        value_names = []
        init_values = []
        petri_goals = []
        place2var = {}
        if goal.parts:
            pddl_goals = goal.parts
        else:
            pddl_goals = [goal]
        for place in self.places:
            place2var[place.name] = len(ranges)
            ranges.append(2)
            axiom_layers.append(-1)
            value_names.append([place.name + '(false)', place.name + '(true)'])
            if place.tokens > 0:
                init_values.append(1)
            else:
                init_values.append(0)
            for goal in pddl_goals:
                if str(goal) == place.name:
                    petri_goals.append((len(ranges) - 1, 1))
                if str(goal.negate()) == place.name:
                    petri_goals.append((len(ranges) - 1, 0))
        variables = sas_tasks.SASVariables(ranges, axiom_layers, value_names)
        mutexes = []
        init = sas_tasks.SASInit(init_values)
        goal = sas_tasks.SASGoal(petri_goals)
        operators = []
        for i, tran in enumerate(self.transitions):
            entered_vars = set()
            pre_post = []
            debug = False
            for orig in tran.origins:
                var = place2var[orig.name]
                pre_val = 1
                post_val = 0
                for dest in tran.destinations:
                    if dest.name == orig.name:
                        post_val = 1
                        break
                # cond is always empty
                pre_post.append((var, pre_val, post_val, []))
                entered_vars.add(var)
            for dest in tran.destinations:
                var = place2var[dest.name]
                if var not in entered_vars:
                    post_val = 1
                    pre_val = 0
                    for orig in tran.origins:
                        if orig.name == dest.name:
                            pre_val = 1
                            break
                    # cond is always empty
                    pre_post.append((var, pre_val, post_val, []))
            # prevail is always empty list, all preconditions to preconds
            operators.append(sas_tasks.SASOperator(
                f"({tran.name})", [], pre_post, tran.cost))
        axioms = []
        metric = True
        sas_task = sas_tasks.SASTask(variables, mutexes, init, goal,
                                     operators, axioms, metric)
        sas_task.output(output)
