#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  // Create a solver instance using stp as the backend
  SmtSolver solver = StpSolverFactory::create(false);

  // Create sorts for bit-vectors and Booleans
  Sort bvsort8 = solver->make_sort(BV, 8);  // 8-bit bit-vector
  Sort boolsort = solver->make_sort(BOOL); // Boolean sort

  // Create bit-vector variables
  Term x = solver->make_symbol("x", bvsort8);
  Term y = solver->make_symbol("y", bvsort8);

  // Create a Boolean variable
  Term b = solver->make_symbol("b", boolsort);

  // Define constraints
  Term x_plus_y = solver->make_term(BVAdd, x, y);             // x + y
  Term constraint1 = solver->make_term(Equal, x_plus_y, x);   // x + y == x
  Term constraint2 = solver->make_term(Equal, b, solver->make_term(BVUge, x, y)); // b == (x >= y)

  // Assert the constraints to the solver
  solver->assert_formula(constraint1);
  solver->assert_formula(constraint2);

  // Check satisfiability
  Result result = solver->check_sat();
  if (result.is_sat()) {
	  cout << "SAT" << endl;

	  // Get values of variables
	  cout << "x: " << solver->get_value(x) << endl;
	  cout << "y: " << solver->get_value(y) << endl;
	  cout << "b: " << solver->get_value(b) << endl1;
  } else if (result.is_unsat()) {
	  cout << "UNSAT" << endl;
  } else {
	  cout << "UNKNOWN" << endl;
  }

  return 0;
}