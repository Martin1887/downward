#include "dihgar_task.h"

#include "dihgar.h"
#include "dihgar_step.h"

#include <memory>
#include <vector>

using namespace std;

namespace cegar {
DihgarTask::DihgarTask(
    const vector<shared_ptr<DihgarStep>> &steps)
    : steps(steps) {
}

const vector<shared_ptr<DihgarStep>> DihgarTask::get_steps() const {
    return steps;
}

void DihgarTask::run(shared_ptr<DIHGAR> dihgar) const {
    if (dihgar->log.is_at_least_normal()) {
        dihgar->log << "Running task with " << steps.size() << " steps" << endl;
    }
    for (shared_ptr<DihgarStep> step : steps) {
        step->run(dihgar);
    }
}

bool DihgarTask::contains_potentials_step() const {
    for (auto step : steps) {
        if (step->contains_potentials()) {
            return true;
        }
    }
    
    return false;
}
}
