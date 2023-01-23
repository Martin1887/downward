#include "dihgar_step.h"

#include "abstract_state.h"
#include "abstraction.h"
#include "cegar.h"
#include "dihgar.h"
#include "types.h"
#include "utils_landmarks.h"

#include "../landmarks/landmark.h"
#include "../landmarks/landmark_factory_h_m.h"
#include "../landmarks/landmark_graph.h"
#include "../potentials/potential_function.h"
#include "../potentials/potential_optimizer.h"

#include <memory>
#include <vector>

using namespace std;
using namespace landmarks;

namespace cegar {
void CegarDihgarStep::run(shared_ptr<DIHGAR> dihgar) const {
    dihgar->log << "Running CEGAR step" << endl;
    CEGAR cegar(
        dihgar->task,
        dihgar->abstraction,
        dihgar->abstract_search,
        dihgar->max_states,
        dihgar->max_non_looping_transitions,
        dihgar->timer.get_remaining_time(),
        dihgar->pick,
        dihgar->rng,
        dihgar->log);
}

void RefinedByFactsDihgarStep::run(shared_ptr<DIHGAR> dihgar) const {
    if (dihgar->log.is_at_least_normal()) {
        dihgar->log << "Running step " << typeid(this).name() << endl;
    }
    const vector<FactPair> refined_facts = get_refined_facts(dihgar);
    refine_by_facts(dihgar, refined_facts);
    // Shrinking does not pays off because the overhead
    // over the refinement hierarchy.
    // shrink(dihgar);
}

void RefinedByFactsDihgarStep::refine_by_facts(
    shared_ptr<DIHGAR> dihgar,
    const vector<FactPair> &refined_facts) const {
    if (dihgar->log.is_at_least_normal()) {
        dihgar->log << "Refine by facts " << refined_facts << endl;
    }
    /*
      Two alternative approaches exist here:

      1. Create the initial abstraction already refined creating the states to
         match the the refinement and rewiring then. More complicated and not
         compatible with refinement hierarchy but probably more efficient.
         Abstractions are created fast anyway, so the performance increment of
         this approach does not pay off.

      2. Refine fact by fact from the trivial abstraction. Slower but less
         problematic. In terms of performance, it avoids the flaws searches, so
         it is still more efficient than starting CEGAR from the beginning.
         This is the chosen alternative.
    */
    vector<FactPair> not_refined_yet = vector<FactPair>(refined_facts);
    while (!not_refined_yet.empty()) {
        FactPair to_refine = not_refined_yet.back();

        // Traverse all the abstract states and refine the states that contain
        // the fact to refine.
        AbstractStates all_states = dihgar->abstraction->get_all_states();
        for (auto &st : all_states) {
            // Refine only if the value is in the state and more values exist
            // for the same variable.
            if (st->count(to_refine.var) > 1 &&
                st->contains(to_refine.var, to_refine.value)) {
                auto new_state_ids = dihgar->abstraction->refine(
                    *st, to_refine.var, vector<int>(to_refine.value));
                // Since h-values only increase we can assign the h-value
                // to the children.
                dihgar->abstract_search->copy_h_value_to_children(
                    st->get_id(), new_state_ids.first, new_state_ids.second);
            }
        }

        not_refined_yet.pop_back();
    }
}

const vector<FactPair> FactLandmarksDihgarStep::get_refined_facts(
    shared_ptr<DIHGAR> dihgar) const {
    const shared_ptr<LandmarkGraph> lm_graph = get_landmark_graph(dihgar->task);
    vector<FactPair> landmarks = get_fact_landmarks(*lm_graph);
    return landmarks;
}

AllStatesSmallestPotentialsDihgarStep::AllStatesSmallestPotentialsDihgarStep(
    int fact_potentials_to_refine_number)
    : fact_potentials_to_refine_number(fact_potentials_to_refine_number) {
};

const vector<FactPair> AllStatesSmallestPotentialsDihgarStep::get_refined_facts(
    shared_ptr<DIHGAR> dihgar) const {
    // 'Smallest' is defined as the `fact_potentials_to_refine_number`
    // lowest values
    
    if (dihgar->fact_potentials != nullptr) {
        // Each element of the tuple is `(var, value, potential)`.
        vector<tuple<int, int, double>> potentials;
        for (long unsigned int i = 0; i < dihgar->fact_potentials->size(); i++) {
            for (long unsigned int j = 0;
                j < dihgar->fact_potentials->at(i).size(); j++) {
                potentials.push_back(
                    tuple<int, int, double>(
                        i, j, dihgar->fact_potentials->at(i)[j]));
            }
        }

        // Sort from smallest to largest.
        std::sort(potentials.begin(), potentials.end(),
            [](const tuple<int, int, double> &a,
                const tuple<int, int, double> &b) {
                return get<2>(a) < get<2>(b);
            }
        );

        // Get the elements with the lowest value.
        vector<FactPair> to_refine;
        for (int i = 0;
            i < fact_potentials_to_refine_number && i < int(potentials.size());
            i++) {
            to_refine.emplace_back(get<0>(potentials[i]), get<1>(potentials[i]));
        }

        return to_refine;
    } else {
        dihgar->log <<
            "No fact potentials computed. Remember to override the `has_potentials` function.";
        abort();
    }
}
}