#pragma once

#include "smt_defs.h"

namespace smt {
class StpSolverFactory
{
 public:
  /** Create a stp SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *  @return a stp SmtSolver
   */
  static SmtSolver create(bool logging);
};
}  // namespace smt
