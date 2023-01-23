#ifndef CEGAR_DIHGAR_STRATEGY_H
#define CEGAR_DIHGAR_STRATEGY_H

#include "dihgar_task.h"

#include <memory>
#include <vector>

namespace options {
class Options;
}

namespace utils {
class RandomNumberGenerator;
class LogProxy;
}

namespace cegar {
using DihgarSharedTasks = std::vector<std::shared_ptr<DihgarTask>>;

/*
  Parse the arguments to create a DIHGAR task.
*/
class DihgarStrategy {
public:
    virtual DihgarSharedTasks get_dihgar_tasks(
        utils::LogProxy &log) const = 0;
    virtual ~DihgarStrategy() = default;
};

/*
  Execute the original CEGAR algorithm.
*/
class OriginalCegarStrategy : public DihgarStrategy {
public:
    explicit OriginalCegarStrategy(const options::Options &opts);

    DihgarSharedTasks get_dihgar_tasks(
        utils::LogProxy &log) const override;
};

/*
  Create an intermediate abstraction refining by all fact landmarks.
*/
class FactLandmarksStrategy : public DihgarStrategy {
public:
    explicit FactLandmarksStrategy(const options::Options &opts);

    DihgarSharedTasks get_dihgar_tasks(
        utils::LogProxy &log) const override;
};

/*
  Create an intermediate abstraction refining by the smallest potentials.
*/
class SmallestPotentialsStrategy : public DihgarStrategy {
protected:
    const int fact_potentials_to_refine_number;
public:
    explicit SmallestPotentialsStrategy(const options::Options &opts);

    DihgarSharedTasks get_dihgar_tasks(
        utils::LogProxy &log) const override;
};

/*
  Execute all strategies.
*/
class AllStrategy : public DihgarStrategy {
protected:
    const int fact_potentials_to_refine_number;
public:
    explicit AllStrategy(const options::Options &opts);

    DihgarSharedTasks get_dihgar_tasks(
        utils::LogProxy &log) const override;
};
}

#endif
