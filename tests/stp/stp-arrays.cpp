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
  // Initialize STP solver
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  // Index and element sorts
  Sort idxsort = solver->make_sort(BV, 4);   // 4-bit indices
  Sort elemsort = solver->make_sort(BV, 8);  // 8-bit elements
  Sort arrsort = solver->make_sort(ARRAY, idxsort, elemsort);

  // Array symbol
  Term arr = solver->make_symbol("arr", arrsort);

  // Concrete index/value
  Term idx_five = solver->make_term(5, idxsort);
  Term val_42  = solver->make_term(42, elemsort);

  // Constrain the value at index 5 directly: arr[5] == 42
  Term read_at_five = solver->make_term(Select, arr, idx_five);
  solver->assert_formula(solver->make_term(Equal, read_at_five, val_42));

  // The problem is satisfiable
  Result r = solver->check_sat();
  assert(r.is_sat());

  // Evaluate select expression arr[5] in the model
  Term select_expr = solver->make_term(Select, arr, idx_five);
  Term select_val  = solver->get_value(select_expr);
  assert(select_val->to_int() == 42);

  // Retrieve the concrete array model
  Term const_base;
  UnorderedTermMap assignments = solver->get_array_values(arr, const_base);

  // Expect at least one explicit assignment (index 5 ↦ 42)
  assert(!assignments.empty());
  bool found = false;
  for (auto & p : assignments)
  {
    if (p.first->to_int() == 5)
    {
      assert(p.second->to_int() == 42);
      found = true;
    }
  }
  assert(found);

  // If a constant base was reported, it has element sort BV8
  if (const_base)
  {
    assert(const_base->get_sort() == elemsort);
  }

  cout << "STP array test passed" << endl;
  return 0;
} 