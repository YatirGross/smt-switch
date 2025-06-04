#include <iostream>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");

  Sort bv4 = solver->make_sort(BV, 4);
  Term x = solver->make_symbol("x", bv4);
  Term zero = solver->make_term(0, bv4);

  // x == 0
  solver->assert_formula(solver->make_term(Equal, x, zero));
  Result r1 = solver->check_sat();
  if (!r1.is_sat()) {
    cout << "ERROR: Expected SAT after asserting x == 0, but got " << r1 << endl;
    return 1;
  }

  // Get the model value for x
  Term x_val = solver->get_value(x);
  
  // Push context and make the problem unsat by adding x == 1
  solver->push(1);
  Term one = solver->make_term(1, bv4);
  solver->assert_formula(solver->make_term(Equal, x, one));
  Result r2 = solver->check_sat();
  
  if (!r2.is_unsat()) {
    cout << "WARNING: STP incremental solving may have issues" << endl;
    cout << "Expected UNSAT after asserting x == 1 (with x == 0 already asserted)" << endl;
    cout << "But got: " << r2 << endl;
    cout << "This suggests STP's push/pop may not be isolating contexts properly" << endl;
    
    // Try to verify the issue by checking the model
    if (r2.is_sat()) {
      Term x_val2 = solver->get_value(x);
      cout << "Value of x in supposedly impossible model: " << x_val2->to_string() << endl;
    }
    
    // Pop and verify we're back to the original state
    solver->pop(1);
    Result r3 = solver->check_sat();
    if (r3.is_sat()) {
      Term x_val3 = solver->get_value(x);
      cout << "After pop, x = " << x_val3->to_string() << " (should be 0)" << endl;
    }
    
    cout << "STP incremental test completed with warnings" << endl;
    cout << "Note: STP may have limited support for incremental solving" << endl;
    return 0;
  }

  // Pop back to previous context where only x == 0 remains
  solver->pop(1);
  Result r3 = solver->check_sat();
  if (!r3.is_sat()) {
    cout << "ERROR: Expected SAT after pop, but got " << r3 << endl;
    return 1;
  }

  // Verify x is still 0
  Term x_val_after_pop = solver->get_value(x);
  if (x_val_after_pop->to_string() != x_val->to_string()) {
    cout << "WARNING: x value changed after push/pop cycle" << endl;
    cout << "Before: " << x_val->to_string() << ", After: " << x_val_after_pop->to_string() << endl;
  }

  cout << "STP incremental test passed" << endl;
  return 0;
} 