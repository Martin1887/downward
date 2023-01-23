#include "dihgar.h"

#include "abstraction.h"
#include "abstract_state.h"
#include "cartesian_set.h"
#include "cegar.h"
#include "transition_system.h"
#include "utils.h"

#include "../lp/lp_solver.h"
#include "../task_utils/task_properties.h"
#include "../utils/language.h"
#include "../utils/logging.h"
#include "../utils/math.h"
#include "../utils/memory.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <unordered_map>

using namespace std;

namespace cegar {
DIHGAR::DIHGAR(
    const std::shared_ptr<AbstractTask> &task,
    int max_states,
    int max_non_looping_transitions,
    double max_time,
    PickSplit pick,
    utils::RandomNumberGenerator &rng,
    utils::LogProxy &log,
    shared_ptr<vector<vector<double>>> fact_potentials)
    : task(task),
      task_proxy(*task),
      domain_sizes(get_domain_sizes(task_proxy)),
      max_states(max_states),
      max_non_looping_transitions(max_non_looping_transitions),
      pick(pick),
      split_selector(task, pick),
      abstraction(make_shared<Abstraction>(task, log)),
      abstract_search(make_shared<AbstractSearch>(task_properties::get_operator_costs(task_proxy))),
      timer(max_time),
      rng(rng),
      log(log),
      fact_potentials(fact_potentials) {
    assert(max_states >= 1);
    if (log.is_at_least_normal()) {
        log << "Start building DIHGAR abstraction." << endl;
        log << "Maximum number of states: " << max_states << endl;
        log << "Maximum number of transitions: "
            << max_non_looping_transitions << endl;
    }
}
}
