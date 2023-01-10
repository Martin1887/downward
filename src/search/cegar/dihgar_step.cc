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
        for (auto& st : all_states) {
            if (st->contains(to_refine.var, to_refine.value)) {
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

/*
  Return the fact landmarks as the facts to be refined.
*/
const vector<FactPair> FactLandmarksDihgarStep::get_refined_facts(
    shared_ptr<DIHGAR> dihgar) const {
    const shared_ptr<LandmarkGraph> lm_graph = get_landmark_graph(dihgar->task);
    vector<FactPair> landmarks = get_fact_landmarks(*lm_graph);
    return landmarks;
}
}