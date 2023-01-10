#ifndef CEGAR_DIHGAR_TASK_H
#define CEGAR_DIHGAR_TASK_H

#include "dihgar.h"
#include "dihgar_step.h"

#include <memory>
#include <vector>

using namespace std;

namespace cegar {
/*
  A DIHGAR task contains the ordered steps to refine the trivial abstraction.
  Usually a CEGAR refinement is executed after one or more domain independent
  heuristic guided refinements, the first of them is executed upon the trivial
  abstraction.
*/
class DihgarTask {
    const vector<shared_ptr<DihgarStep>> steps;

public:
    DihgarTask(const vector<shared_ptr<DihgarStep>> &steps);
    ~DihgarTask() = default;

    const vector<shared_ptr<DihgarStep>> get_steps() const;

    void run(shared_ptr<DIHGAR> dihgar) const;
};
}

#endif
