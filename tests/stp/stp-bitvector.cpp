#include <iostream>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = StpSolverFactory::create(false);
  s->set_logic("QF_BV");
  s->set_opt("produce-models", "true");

  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term y = s->make_symbol("y", bv8);

  Term five = s->make_term(5, bv8);
  Term shift_amt = s->make_term(1, bv8);   // used as BV for shift

  // Constrain x = 5
  s->assert_formula(s->make_term(Equal, x, five));
  std::cout << "x = 5" << std::endl;
  // y = (x << 1)
  Term shl = s->make_term(BVShl, x, shift_amt);
  s->assert_formula(s->make_term(Equal, y, shl));
  std::cout << "y = (x << 1)" << std::endl;

  // Additionally, y == 10 should hold
  Term ten = s->make_term(10, bv8);
  s->assert_formula(s->make_term(Equal, y, ten));

  Result r = s->check_sat();
  assert(r.is_sat());
  std::cout << "sat" << std::endl;
  Term y_val = s->get_value(y);
  assert(y_val->to_int() == 10);
  std::cout << "y_val = " << y_val->to_int() << std::endl;
  // Now create an unsat branch: add x + 1 == x
  s->push(1);
  Term add_expr = s->make_term(BVAdd, x, s->make_term(1, bv8));
  s->assert_formula(s->make_term(Equal, x, add_expr));
  Result r_unsat = s->check_sat();
  assert(r_unsat.is_unsat());
  s->pop(1);

  cout << "STP bitvector test passed" << endl;
  return 0;
} 