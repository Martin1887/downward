#ifndef CEGAR_DIHGAR_H
#define CEGAR_DIHGAR_H

#include "cegar.h"

#include "../abstract_task.h"
#include "../lp/lp_solver.h"

using namespace std;

namespace cegar {
/*
  DIHGAR data, used in all the steps of the task, the last of them
  usually is the CEGAR refinement upon the abstraction generated refining by
  domain independent heuristics in the previous steps instead of the trivial
  abstraction.
*/
class DIHGAR {
public:
    const shared_ptr<AbstractTask> task;
    const TaskProxy task_proxy;
    const std::vector<int> domain_sizes;
    const int max_states;
    const int max_non_looping_transitions;
    const PickSplit pick;
    const SplitSelector split_selector;

    std::shared_ptr<Abstraction> abstraction;
    std::shared_ptr<AbstractSearch> abstract_search;

    // Limit the time for building the abstraction.
    utils::CountdownTimer timer;

    utils::RandomNumberGenerator &rng;

    utils::LogProxy &log;

    std::shared_ptr<std::vector<std::vector<double>>> fact_potentials;

    DIHGAR(
        const std::shared_ptr<AbstractTask> &task,
        int max_states,
        int max_non_looping_transitions,
        double max_time,
        PickSplit pick,
        utils::RandomNumberGenerator &rng,
        utils::LogProxy &log,
        std::shared_ptr<std::vector<std::vector<double>>> fact_potentials);
    ~DIHGAR() = default;

    DIHGAR(DIHGAR &) = delete;
};
}

#endif
