#include "stp_factory.h"
#include "stp_solver.h"
#include "logging_solver.h"

namespace smt {

/* StpSolverFactory implementation */
SmtSolver StpSolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<StpSolver>();
  return solver;
}

/* end StpSolverFactory implementation */

}  // namespace smt
