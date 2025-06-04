/*********************                                                        */
/*! \file stp-basic-bool.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Basic boolean tests for STP solver
**        Tests fundamental boolean operations, constants, and satisfiability
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_boolean_constants()
{
  cout << "=== Testing Boolean Constants ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  // Test true constant
  Term true_term = solver->make_term(true);
  assert(true_term);
  
  // Test false constant  
  Term false_term = solver->make_term(false);
  assert(false_term);
  
  // Test that true != false
  assert(true_term != false_term);
  
  // Test satisfiability with true
  solver->push(1);
  solver->assert_formula(true_term);
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test satisfiability with false
  solver->push(1);
  solver->assert_formula(false_term);
  r = solver->check_sat();
  assert(r.is_unsat());
  solver->pop(1);
  
  cout << "Boolean constants test PASSED" << endl;
}

void test_boolean_variables()
{
  cout << "=== Testing Boolean Variables ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Create boolean variables
  Term a = solver->make_symbol("a", bool_sort);
  Term b = solver->make_symbol("b", bool_sort);
  Term c = solver->make_symbol("c", bool_sort);
  
  // Test that variables are distinct
  assert(a != b);
  assert(b != c);
  assert(a != c);
  
  // Test satisfiability with single variable
  solver->push(1);
  solver->assert_formula(a);
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term a_val = solver->get_value(a);
  assert(a_val->to_int() == 1); // true
  solver->pop(1);
  
  // Test satisfiability with negated variable
  solver->push(1);
  Term not_a = solver->make_term(Not, a);
  solver->assert_formula(not_a);
  r = solver->check_sat();
  assert(r.is_sat());
  
  a_val = solver->get_value(a);
  assert(a_val->to_int() == 0); // false
  solver->pop(1);
  
  cout << "Boolean variables test PASSED" << endl;
}

void test_basic_boolean_operations()
{
  cout << "=== Testing Basic Boolean Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term a = solver->make_symbol("a", bool_sort);
  Term b = solver->make_symbol("b", bool_sort);
  
  // Test AND operation
  Term and_term = solver->make_term(And, a, b);
  
  // a=true, b=true => a AND b = true
  solver->push(1);
  solver->assert_formula(a);
  solver->assert_formula(b);
  solver->assert_formula(and_term);
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // a=true, b=false => a AND b = false
  solver->push(1);
  solver->assert_formula(a);
  solver->assert_formula(solver->make_term(Not, b));
  solver->assert_formula(solver->make_term(Not, and_term));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test OR operation
  Term or_term = solver->make_term(Or, a, b);
  
  // a=false, b=false => a OR b = false
  solver->push(1);
  solver->assert_formula(solver->make_term(Not, a));
  solver->assert_formula(solver->make_term(Not, b));
  solver->assert_formula(solver->make_term(Not, or_term));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // a=true, b=false => a OR b = true
  solver->push(1);
  solver->assert_formula(a);
  solver->assert_formula(solver->make_term(Not, b));
  solver->assert_formula(or_term);
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "Basic boolean operations test PASSED" << endl;
}

void test_boolean_truth_tables()
{
  cout << "=== Testing Boolean Truth Tables ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term a = solver->make_symbol("a", bool_sort);
  Term b = solver->make_symbol("b", bool_sort);
  
  // Test XOR truth table
  Term xor_term = solver->make_term(Xor, a, b);
  
  // XOR should be true when inputs differ
  for (int a_val : {0, 1}) {
    for (int b_val : {0, 1}) {
      solver->push(1);
      
      // Set variable values
      if (a_val) {
        solver->assert_formula(a);
      } else {
        solver->assert_formula(solver->make_term(Not, a));
      }
      
      if (b_val) {
        solver->assert_formula(b);
      } else {
        solver->assert_formula(solver->make_term(Not, b));
      }
      
      // Check XOR result
      bool expected_xor = (a_val != b_val);
      if (expected_xor) {
        solver->assert_formula(xor_term);
      } else {
        solver->assert_formula(solver->make_term(Not, xor_term));
      }
      
      Result r = solver->check_sat();
      assert(r.is_sat());
      
      solver->pop(1);
    }
  }
  
  cout << "Boolean truth tables test PASSED" << endl;
}

void test_boolean_implications()
{
  cout << "=== Testing Boolean Implications ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term a = solver->make_symbol("a", bool_sort);
  Term b = solver->make_symbol("b", bool_sort);
  
  // Test implication: a => b
  Term implies_term = solver->make_term(Implies, a, b);
  
  // When a is false, implication should be true regardless of b
  solver->push(1);
  solver->assert_formula(solver->make_term(Not, a));
  solver->assert_formula(implies_term);
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // When a is true and b is true, implication should be true
  solver->push(1);
  solver->assert_formula(a);
  solver->assert_formula(b);
  solver->assert_formula(implies_term);
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // When a is true and b is false, implication should be false
  solver->push(1);
  solver->assert_formula(a);
  solver->assert_formula(solver->make_term(Not, b));
  solver->assert_formula(solver->make_term(Not, implies_term));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "Boolean implications test PASSED" << endl;
}

void test_boolean_ite()
{
  cout << "=== Testing Boolean ITE (If-Then-Else) ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term cond = solver->make_symbol("cond", bool_sort);
  Term then_val = solver->make_symbol("then_val", bool_sort);
  Term else_val = solver->make_symbol("else_val", bool_sort);
  
  Term ite_term = solver->make_term(Ite, cond, then_val, else_val);
  
  // When condition is true, result should be then_val
  solver->push(1);
  solver->assert_formula(cond);
  solver->assert_formula(then_val);
  solver->assert_formula(solver->make_term(Not, else_val));
  solver->assert_formula(ite_term);
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // When condition is false, result should be else_val
  solver->push(1);
  solver->assert_formula(solver->make_term(Not, cond));
  solver->assert_formula(solver->make_term(Not, then_val));
  solver->assert_formula(else_val);
  solver->assert_formula(ite_term);
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "Boolean ITE test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Basic Boolean Tests..." << endl;
    
    test_boolean_constants();
    test_boolean_variables();
    test_basic_boolean_operations();
    test_boolean_truth_tables();
    test_boolean_implications();
    test_boolean_ite();
    
    cout << "All STP Basic Boolean Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 