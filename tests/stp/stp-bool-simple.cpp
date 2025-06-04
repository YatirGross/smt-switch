/*********************                                                        */
/*! \file stp-bool-simple.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Simple boolean tests for STP solver
**        Tests common boolean patterns and practical satisfiability problems
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_simple_sat_unsat()
{
  cout << "=== Testing Simple SAT/UNSAT Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term p = solver->make_symbol("p", bool_sort);
  
  // Simple SAT case: p OR NOT p (tautology)
  solver->push(1);
  Term not_p = solver->make_term(Not, p);
  Term tautology = solver->make_term(Or, p, not_p);
  solver->assert_formula(tautology);
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Simple UNSAT case: p AND NOT p (contradiction)
  solver->push(1);
  Term contradiction = solver->make_term(And, p, not_p);
  solver->assert_formula(contradiction);
  r = solver->check_sat();
  assert(r.is_unsat());
  solver->pop(1);
  
  cout << "Simple SAT/UNSAT test PASSED" << endl;
}

void test_three_sat_problem()
{
  cout << "=== Testing 3-SAT Problem ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term x1 = solver->make_symbol("x1", bool_sort);
  Term x2 = solver->make_symbol("x2", bool_sort);
  Term x3 = solver->make_symbol("x3", bool_sort);
  
  // 3-SAT formula: (x1 OR x2 OR x3) AND (NOT x1 OR x2 OR NOT x3) AND (x1 OR NOT x2 OR x3)
  Term clause1 = solver->make_term(Or, x1, solver->make_term(Or, x2, x3));
  Term clause2 = solver->make_term(Or, solver->make_term(Not, x1), 
                                   solver->make_term(Or, x2, solver->make_term(Not, x3)));
  Term clause3 = solver->make_term(Or, x1, 
                                   solver->make_term(Or, solver->make_term(Not, x2), x3));
  
  solver->push(1);
  solver->assert_formula(clause1);
  solver->assert_formula(clause2);
  solver->assert_formula(clause3);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Get and verify solution
  Term x1_val = solver->get_value(x1);
  Term x2_val = solver->get_value(x2);
  Term x3_val = solver->get_value(x3);
  
  cout << "Solution: x1=" << x1_val->to_int() 
       << ", x2=" << x2_val->to_int() 
       << ", x3=" << x3_val->to_int() << endl;
  
  solver->pop(1);
  
  cout << "3-SAT problem test PASSED" << endl;
}

void test_boolean_circuit()
{
  cout << "=== Testing Boolean Circuit ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Inputs
  Term a = solver->make_symbol("a", bool_sort);
  Term b = solver->make_symbol("b", bool_sort);
  Term c = solver->make_symbol("c", bool_sort);
  
  // Gates
  Term and_gate = solver->make_term(And, a, b);
  Term or_gate = solver->make_term(Or, b, c);
  Term xor_gate = solver->make_term(Xor, and_gate, or_gate);
  
  // Output constraint: circuit should output true
  solver->push(1);
  solver->assert_formula(xor_gate);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term a_val = solver->get_value(a);
  Term b_val = solver->get_value(b);
  Term c_val = solver->get_value(c);
  Term output_val = solver->get_value(xor_gate);
  
  assert(output_val->to_int() == 1); // Circuit outputs true
  
  cout << "Circuit inputs: a=" << a_val->to_int() 
       << ", b=" << b_val->to_int() 
       << ", c=" << c_val->to_int() << endl;
  
  solver->pop(1);
  
  cout << "Boolean circuit test PASSED" << endl;
}

void test_mutex_constraints()
{
  cout << "=== Testing Mutual Exclusion Constraints ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Three mutually exclusive flags
  Term flag1 = solver->make_symbol("flag1", bool_sort);
  Term flag2 = solver->make_symbol("flag2", bool_sort);
  Term flag3 = solver->make_symbol("flag3", bool_sort);
  
  // At most one can be true
  Term not_12 = solver->make_term(Not, solver->make_term(And, flag1, flag2));
  Term not_13 = solver->make_term(Not, solver->make_term(And, flag1, flag3));
  Term not_23 = solver->make_term(Not, solver->make_term(And, flag2, flag3));
  
  // At least one must be true
  Term at_least_one = solver->make_term(Or, flag1, solver->make_term(Or, flag2, flag3));
  
  solver->push(1);
  solver->assert_formula(not_12);
  solver->assert_formula(not_13);
  solver->assert_formula(not_23);
  solver->assert_formula(at_least_one);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term flag1_val = solver->get_value(flag1);
  Term flag2_val = solver->get_value(flag2);
  Term flag3_val = solver->get_value(flag3);
  
  // Verify exactly one flag is true
  int count = flag1_val->to_int() + flag2_val->to_int() + flag3_val->to_int();
  assert(count == 1);
  
  cout << "Mutex solution: flag1=" << flag1_val->to_int() 
       << ", flag2=" << flag2_val->to_int() 
       << ", flag3=" << flag3_val->to_int() << endl;
  
  solver->pop(1);
  
  cout << "Mutual exclusion test PASSED" << endl;
}

void test_implication_chains()
{
  cout << "=== Testing Implication Chains ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term p1 = solver->make_symbol("p1", bool_sort);
  Term p2 = solver->make_symbol("p2", bool_sort);
  Term p3 = solver->make_symbol("p3", bool_sort);
  Term p4 = solver->make_symbol("p4", bool_sort);
  
  // Chain: p1 => p2 => p3 => p4
  Term imp1 = solver->make_term(Implies, p1, p2);
  Term imp2 = solver->make_term(Implies, p2, p3);
  Term imp3 = solver->make_term(Implies, p3, p4);
  
  solver->push(1);
  solver->assert_formula(imp1);
  solver->assert_formula(imp2);
  solver->assert_formula(imp3);
  solver->assert_formula(p1); // Start the chain
  solver->assert_formula(p4); // End should be true
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // All should be true due to the chain
  Term p1_val = solver->get_value(p1);
  Term p2_val = solver->get_value(p2);
  Term p3_val = solver->get_value(p3);
  Term p4_val = solver->get_value(p4);
  
  assert(p1_val->to_int() == 1);
  assert(p2_val->to_int() == 1);
  assert(p3_val->to_int() == 1);
  assert(p4_val->to_int() == 1);
  
  solver->pop(1);
  
  cout << "Implication chains test PASSED" << endl;
}

void test_conditional_logic()
{
  cout << "=== Testing Conditional Logic ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term condition = solver->make_symbol("condition", bool_sort);
  Term action1 = solver->make_symbol("action1", bool_sort);
  Term action2 = solver->make_symbol("action2", bool_sort);
  Term result = solver->make_symbol("result", bool_sort);
  
  // If condition then action1, else action2
  Term then_branch = solver->make_term(And, condition, action1);
  Term else_branch = solver->make_term(And, solver->make_term(Not, condition), action2);
  Term conditional = solver->make_term(Or, then_branch, else_branch);
  
  // Result should match the taken action
  Term result_condition = solver->make_term(Ite, condition, 
                                           solver->make_term(Equal, result, action1),
                                           solver->make_term(Equal, result, action2));
  
  solver->push(1);
  solver->assert_formula(conditional);
  solver->assert_formula(result_condition);
  solver->assert_formula(condition); // Take true branch
  solver->assert_formula(action1);   // Action1 is true
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term result_val = solver->get_value(result);
  assert(result_val->to_int() == 1); // Result should be true (same as action1)
  
  solver->pop(1);
  
  cout << "Conditional logic test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Simple Boolean Tests..." << endl;
    
    test_simple_sat_unsat();
    test_three_sat_problem();
    test_boolean_circuit();
    test_mutex_constraints();
    test_implication_chains();
    test_conditional_logic();
    
    cout << "All STP Simple Boolean Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 