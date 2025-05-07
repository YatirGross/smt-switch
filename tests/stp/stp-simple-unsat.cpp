#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

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
  Term three = solver->make_term(3, bvsort8);

  // Define constraints
  Term x_plus_y = solver->make_term(BVAdd, x, y);             // x + y
  Term constraint1 = solver->make_term(Equal, x_plus_y, three);   // x + y == 3
  Term constraint2 = solver->make_term(Equal, x, y); // x == y
  

  // Assert the constraints to the solver
  solver->assert_formula(constraint1);
  solver->assert_formula(constraint2);

  // Check satisfiability
  Result result = solver->check_sat();
  if (result.is_sat()) {
	  cout << "SAT" << endl;

	  // Get the value of x
    Term x_val = solver->get_value(x);
    Term y_val = solver->get_value(y);
    cout << "x = " << x_val->to_int() << endl;
    cout << "y = " << y_val->to_int() << endl;
  } else if (result.is_unsat()) {
	  cout << "UNSAT" << endl;
  } else {
	  cout << "UNKNOWN" << endl;
  }

  return 0;
}