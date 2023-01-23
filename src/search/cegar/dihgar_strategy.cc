#include "dihgar_strategy.h"

#include "dihgar_step.h"
#include "dihgar_task.h"
#include "utils.h"
#include "utils_landmarks.h"

#include "../option_parser.h"
#include "../plugin.h"

#include <vector>

using namespace std;

namespace cegar {
OriginalCegarStrategy::OriginalCegarStrategy(const Options &opts) {
    utils::unused_variable(opts);
}

DihgarSharedTasks OriginalCegarStrategy::get_dihgar_tasks(
    utils::LogProxy &log) const {
    if (log.is_at_least_normal()) {
        log << "Original CEGAR strategy starts" << endl;
    }
    DihgarSharedTasks dihgar_tasks;
    vector<shared_ptr<DihgarStep>> steps;
    steps.push_back(make_shared<CegarDihgarStep>());
    shared_ptr<DihgarTask> task = make_shared<DihgarTask>(steps);
    dihgar_tasks.push_back(task);

    return dihgar_tasks;
}

FactLandmarksStrategy::FactLandmarksStrategy(const Options &opts) {
    utils::unused_variable(opts);
}

DihgarSharedTasks FactLandmarksStrategy::get_dihgar_tasks(
    utils::LogProxy &log) const {
    if (log.is_at_least_normal()) {
        log << "Fact landmarks strategy starts" << endl;
    }
    DihgarSharedTasks dihgar_tasks;
    vector<shared_ptr<DihgarStep>> steps;
    steps.push_back(make_shared<FactLandmarksDihgarStep>());
    steps.push_back(make_shared<CegarDihgarStep>());
    shared_ptr<DihgarTask> task = make_shared<DihgarTask>(steps);
    dihgar_tasks.push_back(task);

    return dihgar_tasks;
}

SmallestPotentialsStrategy::SmallestPotentialsStrategy(const Options &opts)
    : fact_potentials_to_refine_number(opts.get<int>("fact_potentials")) {
}

DihgarSharedTasks SmallestPotentialsStrategy::get_dihgar_tasks(
    utils::LogProxy &log) const {
    if (log.is_at_least_normal()) {
        log << "Smallest potentials strategy starts" << endl;
    }
    DihgarSharedTasks dihgar_tasks;
    vector<shared_ptr<DihgarStep>> steps;
    steps.push_back(make_shared<AllStatesSmallestPotentialsDihgarStep>(
                        fact_potentials_to_refine_number
                        ));
    steps.push_back(make_shared<CegarDihgarStep>());
    shared_ptr<DihgarTask> task = make_shared<DihgarTask>(steps);
    dihgar_tasks.push_back(task);

    return dihgar_tasks;
}

AllStrategy::AllStrategy(const Options &opts)
    : fact_potentials_to_refine_number(opts.get<int>("fact_potentials")) {
}

DihgarSharedTasks AllStrategy::get_dihgar_tasks(
    utils::LogProxy &log) const {
    if (log.is_at_least_normal()) {
        log << "All strategy starts" << endl;
    }
    DihgarSharedTasks dihgar_tasks;
    vector<shared_ptr<DihgarStep>> steps;
    steps.push_back(make_shared<FactLandmarksDihgarStep>());
    steps.push_back(make_shared<AllStatesSmallestPotentialsDihgarStep>(
                        fact_potentials_to_refine_number
                        ));
    steps.push_back(make_shared<CegarDihgarStep>());
    shared_ptr<DihgarTask> task = make_shared<DihgarTask>(steps);
    dihgar_tasks.push_back(task);

    return dihgar_tasks;
}

static shared_ptr<DihgarStrategy> _parse_only_cegar(OptionParser &parser) {
    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<OriginalCegarStrategy>(opts);
}

static shared_ptr<DihgarStrategy> _parse_fact_landmarks(OptionParser &parser) {
    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<FactLandmarksStrategy>(opts);
}

static shared_ptr<DihgarStrategy> _parse_smallest_potentials(OptionParser &parser) {
    parser.add_option<int>(
        "fact_potentials",
        "number of fact potentials to refine",
        "10",
        Bounds("1", "infinity"));
    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<SmallestPotentialsStrategy>(opts);
}

static shared_ptr<DihgarStrategy> _parse_all(OptionParser &parser) {
    parser.add_option<int>(
        "fact_potentials",
        "number of fact potentials to refine",
        "10",
        Bounds("1", "infinity"));
    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<AllStrategy>(opts);
}

static Plugin<DihgarStrategy> _plugin_only_cegar(
    "only_cegar", _parse_only_cegar);
static Plugin<DihgarStrategy> _plugin_fact_landmarks(
    "fact_landmarks", _parse_fact_landmarks);
static Plugin<DihgarStrategy> _plugin_smallest_potentials(
    "smallest_potentials", _parse_smallest_potentials);
static Plugin<DihgarStrategy> _plugin_all(
    "all", _parse_all);

static PluginTypePlugin<DihgarStrategy> _type_plugin(
    "DihgarStrategy",
    "Dihgar strategy (used by the CEGAR heuristic).");
}
