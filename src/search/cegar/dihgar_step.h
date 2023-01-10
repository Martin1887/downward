#ifndef CEGAR_DIHGAR_STEP_H
#define CEGAR_DIHGAR_STEP_H

#include "dihgar.h"
#include "utils.h"

#include <memory>
#include <vector>

namespace cegar {
/*
  A shared_ptr<DIHGAR> step is a domain independent heuristic guided refinement upon the
  trivial abstraction or a previously refined abstraction.
*/
class DihgarStep {
public:
    virtual void run(shared_ptr<DIHGAR> dihgar) const {
        utils::unused_variable(dihgar);
    }

    virtual ~DihgarStep() = default;
};

/*
  A CEGAR step simply executes the CEGAR refinement.
*/
class CegarDihgarStep : public DihgarStep {
public:
    CegarDihgarStep() = default;
    CegarDihgarStep(CegarDihgarStep const &) = default;
    void run(shared_ptr<DIHGAR> dihgar) const override;
};

/*
  RefinedByFacts steps guide the refinement choosing a set of facts whose value
  must be uniquely in the whole abstraction. This is, the value of its
  variable must be isolated for all the combinations of the other variables,
  being irrelevant the abstractions of the other values. For instance, if a
  variable V has 4 possible values v1, v2, v3 and v4 and the fact v2 is expanded
  then for all the combinations of other variables the v2 must be the unique
  option in one state, being v1, v3 and v4 in one or more states for the same
  combination of the other variables.

  The `get_refined_facts` method defines the facts to be expanded and it is the
  unique one implemented in each concrete class. The `refine_by_facts` method
  expand the abstraction for the facts chosen in that method and the `shrink`
  method abstracts the irrelevant states after the refinement (the states
  with the same `h` value and the same values in all variables except one,
  which states are combined in a single one). However, the shrinking step
  is omitted because its overhead over the refinement hierarchy does not
  pay off.
*/
class RefinedByFactsDihgarStep : public DihgarStep {
public:
    virtual ~RefinedByFactsDihgarStep() = default;
    RefinedByFactsDihgarStep() = default;
    RefinedByFactsDihgarStep(RefinedByFactsDihgarStep const &) = default;

    void refine_by_facts(
        shared_ptr<DIHGAR> dihgar,
        const vector<FactPair> &refined_facts) const;

    // The overhead of shrinking in the nodes and refinement hierarchy
    // does not pay off.
    // void shrink(shared_ptr<DIHGAR> dihgar) const;
    // void shrink_loop(shared_ptr<DIHGAR> dihgar) const;
    void run(shared_ptr<DIHGAR> dihgar) const override;

    virtual const vector<FactPair> get_refined_facts(shared_ptr<DIHGAR> dihgar) const = 0;
};

/*
  Refine all the fact landmarks.
*/
class FactLandmarksDihgarStep : public RefinedByFactsDihgarStep {
public:
    FactLandmarksDihgarStep() = default;
    FactLandmarksDihgarStep(FactLandmarksDihgarStep const &) = default;
    const vector<FactPair> get_refined_facts(shared_ptr<DIHGAR> dihgar) const override;
};
}

#endif
