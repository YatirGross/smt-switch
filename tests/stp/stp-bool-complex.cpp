/*********************                                                        */
/*! \file stp-bool-complex.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Complex boolean tests for STP solver
**        Tests complex boolean formulas, nested operations, and edge cases
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_nested_boolean_operations()
{
  cout << "=== Testing Nested Boolean Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term a = solver->make_symbol("a", bool_sort);
  Term b = solver->make_symbol("b", bool_sort);
  Term c = solver->make_symbol("c", bool_sort);
  Term d = solver->make_symbol("d", bool_sort);
  
  // Complex nested formula: ((a AND b) OR (c AND d)) XOR (a IMPLIES (b OR c))
  Term ab = solver->make_term(And, a, b);
  Term cd = solver->make_term(And, c, d);
  Term ab_or_cd = solver->make_term(Or, ab, cd);
  
  Term bc = solver->make_term(Or, b, c);
  Term a_implies_bc = solver->make_term(Implies, a, bc);
  
  Term complex_formula = solver->make_term(Xor, ab_or_cd, a_implies_bc);
  
  solver->push(1);
  solver->assert_formula(complex_formula);
  
  // Add constraints to make it satisfiable and interesting
  solver->assert_formula(a);
  solver->assert_formula(solver->make_term(Not, b));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term a_val = solver->get_value(a);
  Term b_val = solver->get_value(b);
  Term c_val = solver->get_value(c);
  Term d_val = solver->get_value(d);
  
  cout << "Solution: a=" << a_val->to_int() << ", b=" << b_val->to_int() 
       << ", c=" << c_val->to_int() << ", d=" << d_val->to_int() << endl;
  
  solver->pop(1);
  
  cout << "Nested boolean operations test PASSED" << endl;
}

void test_boolean_equivalence_checking()
{
  cout << "=== Testing Boolean Equivalence Checking ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term x = solver->make_symbol("x", bool_sort);
  Term y = solver->make_symbol("y", bool_sort);
  
  // Check if two formulas are equivalent: (x AND y) ≡ NOT(NOT x OR NOT y) (De Morgan's law)
  Term formula1 = solver->make_term(And, x, y);
  Term not_x = solver->make_term(Not, x);
  Term not_y = solver->make_term(Not, y);
  Term not_x_or_not_y = solver->make_term(Or, not_x, not_y);
  Term formula2 = solver->make_term(Not, not_x_or_not_y);
  
  // Check equivalence by asserting their XOR should be UNSAT
  Term xor_formulas = solver->make_term(Xor, formula1, formula2);
  
  solver->push(1);
  solver->assert_formula(xor_formulas);
  
  Result r = solver->check_sat();
  assert(r.is_unsat()); // They should be equivalent, so XOR is UNSAT
  
  solver->pop(1);
  
  cout << "Boolean equivalence checking test PASSED" << endl;
}

void test_quantified_boolean_patterns()
{
  cout << "=== Testing Quantified Boolean Patterns ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Simulate universal quantification pattern: for all x1,x2,x3: at least one is true
  // This is equivalent to: NOT((NOT x1) AND (NOT x2) AND (NOT x3))
  vector<Term> vars;
  for (int i = 1; i <= 5; i++) {
    string name = "x" + to_string(i);
    vars.push_back(solver->make_symbol(name, bool_sort));
  }
  
  // Pattern: at least 3 out of 5 variables must be true
  vector<Term> constraints;
  
  // Generate all combinations of 3 variables being true
  for (int i = 0; i < 5; i++) {
    for (int j = i+1; j < 5; j++) {
      for (int k = j+1; k < 5; k++) {
        Term three_true = solver->make_term(And, vars[i], solver->make_term(And, vars[j], vars[k]));
        constraints.push_back(three_true);
      }
    }
  }
  
  // At least one combination should be true
  Term at_least_three = constraints[0];
  for (size_t i = 1; i < constraints.size(); i++) {
    at_least_three = solver->make_term(Or, at_least_three, constraints[i]);
  }
  
  solver->push(1);
  solver->assert_formula(at_least_three);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  int true_count = 0;
  for (int i = 0; i < 5; i++) {
    Term val = solver->get_value(vars[i]);
    if (val->to_int() == 1) true_count++;
    cout << "x" << (i+1) << "=" << val->to_int() << " ";
  }
  cout << endl;
  assert(true_count >= 3);
  
  solver->pop(1);
  
  cout << "Quantified boolean patterns test PASSED" << endl;
}

void test_boolean_circuit_synthesis()
{
  cout << "=== Testing Boolean Circuit Synthesis ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Input variables
  Term in1 = solver->make_symbol("in1", bool_sort);
  Term in2 = solver->make_symbol("in2", bool_sort);
  Term in3 = solver->make_symbol("in3", bool_sort);
  
  // Intermediate gate outputs
  Term gate1_out = solver->make_symbol("gate1_out", bool_sort);
  Term gate2_out = solver->make_symbol("gate2_out", bool_sort);
  Term gate3_out = solver->make_symbol("gate3_out", bool_sort);
  
  // Final output
  Term output = solver->make_symbol("output", bool_sort);
  
  // Circuit constraints
  // gate1: XOR(in1, in2)
  solver->push(1);
  Term gate1_spec = solver->make_term(Equal, gate1_out, solver->make_term(Xor, in1, in2));
  solver->assert_formula(gate1_spec);
  
  // gate2: AND(gate1_out, in3)
  Term gate2_spec = solver->make_term(Equal, gate2_out, solver->make_term(And, gate1_out, in3));
  solver->assert_formula(gate2_spec);
  
  // gate3: OR(gate2_out, in1)
  Term gate3_spec = solver->make_term(Equal, gate3_out, solver->make_term(Or, gate2_out, in1));
  solver->assert_formula(gate3_spec);
  
  // Output: NOT(gate3_out)
  Term output_spec = solver->make_term(Equal, output, solver->make_term(Not, gate3_out));
  solver->assert_formula(output_spec);
  
  // Synthesis constraint: find inputs such that output is true
  solver->assert_formula(output);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term in1_val = solver->get_value(in1);
  Term in2_val = solver->get_value(in2);
  Term in3_val = solver->get_value(in3);
  Term output_val = solver->get_value(output);
  
  cout << "Circuit synthesis: in1=" << in1_val->to_int() 
       << ", in2=" << in2_val->to_int() 
       << ", in3=" << in3_val->to_int() 
       << " => output=" << output_val->to_int() << endl;
  
  assert(output_val->to_int() == 1);
  
  solver->pop(1);
  
  cout << "Boolean circuit synthesis test PASSED" << endl;
}

void test_boolean_satisfiability_phases()
{
  cout << "=== Testing Boolean Satisfiability Phases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  vector<Term> phase_vars;
  
  // Create 8 phase variables
  for (int i = 0; i < 8; i++) {
    string name = "phase" + to_string(i);
    phase_vars.push_back(solver->make_symbol(name, bool_sort));
  }
  
  // Phase transition constraints: exactly one phase can be active at a time
  vector<Term> mutual_exclusion;
  for (int i = 0; i < 8; i++) {
    for (int j = i+1; j < 8; j++) {
      Term not_both = solver->make_term(Not, solver->make_term(And, phase_vars[i], phase_vars[j]));
      mutual_exclusion.push_back(not_both);
    }
  }
  
  // At least one phase must be active
  Term at_least_one = phase_vars[0];
  for (int i = 1; i < 8; i++) {
    at_least_one = solver->make_term(Or, at_least_one, phase_vars[i]);
  }
  
  // Sequential constraint: phases follow a specific order
  vector<Term> sequence_constraints;
  for (int i = 0; i < 7; i++) {
    // If phase i is active, then either phase i or phase i+1 can be next
    Term current_or_next = solver->make_term(Or, phase_vars[i], phase_vars[i+1]);
    Term sequence_constraint = solver->make_term(Implies, phase_vars[i], current_or_next);
    sequence_constraints.push_back(sequence_constraint);
  }
  
  solver->push(1);
  
  // Assert all constraints
  for (const auto& constraint : mutual_exclusion) {
    solver->assert_formula(constraint);
  }
  solver->assert_formula(at_least_one);
  
  for (const auto& constraint : sequence_constraints) {
    solver->assert_formula(constraint);
  }
  
  // Force a specific phase to be active
  solver->assert_formula(phase_vars[3]);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Active phases: ";
  int active_count = 0;
  for (int i = 0; i < 8; i++) {
    Term val = solver->get_value(phase_vars[i]);
    if (val->to_int() == 1) {
      cout << i << " ";
      active_count++;
    }
  }
  cout << endl;
  assert(active_count == 1); // Exactly one phase should be active
  
  solver->pop(1);
  
  cout << "Boolean satisfiability phases test PASSED" << endl;
}

void test_boolean_optimization_problem()
{
  cout << "=== Testing Boolean Optimization Problem ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Decision variables: which items to select
  vector<Term> selected;
  for (int i = 0; i < 6; i++) {
    string name = "item" + to_string(i);
    selected.push_back(solver->make_symbol(name, bool_sort));
  }
  
  // Constraint 1: Cannot select conflicting items
  // item0 conflicts with item2, item1 conflicts with item4
  Term conflict1 = solver->make_term(Not, solver->make_term(And, selected[0], selected[2]));
  Term conflict2 = solver->make_term(Not, solver->make_term(And, selected[1], selected[4]));
  
  // Constraint 2: If item3 is selected, then item5 must also be selected
  Term dependency = solver->make_term(Implies, selected[3], selected[5]);
  
  // Constraint 3: At least 2 items must be selected
  vector<Term> at_least_two_combinations;
  for (int i = 0; i < 6; i++) {
    for (int j = i+1; j < 6; j++) {
      at_least_two_combinations.push_back(solver->make_term(And, selected[i], selected[j]));
    }
  }
  
  Term at_least_two = at_least_two_combinations[0];
  for (size_t i = 1; i < at_least_two_combinations.size(); i++) {
    at_least_two = solver->make_term(Or, at_least_two, at_least_two_combinations[i]);
  }
  
  solver->push(1);
  solver->assert_formula(conflict1);
  solver->assert_formula(conflict2);
  solver->assert_formula(dependency);
  solver->assert_formula(at_least_two);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Selected items: ";
  int selected_count = 0;
  for (int i = 0; i < 6; i++) {
    Term val = solver->get_value(selected[i]);
    if (val->to_int() == 1) {
      cout << i << " ";
      selected_count++;
    }
  }
  cout << endl;
  assert(selected_count >= 2);
  
  solver->pop(1);
  
  cout << "Boolean optimization problem test PASSED" << endl;
}

void test_complex_boolean_invariants()
{
  cout << "=== Testing Complex Boolean Invariants ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // State variables for two time steps
  vector<Term> state_t0, state_t1;
  for (int i = 0; i < 4; i++) {
    state_t0.push_back(solver->make_symbol("s" + to_string(i) + "_t0", bool_sort));
    state_t1.push_back(solver->make_symbol("s" + to_string(i) + "_t1", bool_sort));
  }
  
  // Invariant: at most 2 state variables can be true at any time
  auto at_most_two = [&](const vector<Term>& vars) -> Term {
    vector<Term> three_or_more;
    for (int i = 0; i < 4; i++) {
      for (int j = i+1; j < 4; j++) {
        for (int k = j+1; k < 4; k++) {
          Term three_true = solver->make_term(And, vars[i], 
                                            solver->make_term(And, vars[j], vars[k]));
          three_or_more.push_back(three_true);
        }
      }
    }
    
    if (three_or_more.empty()) {
      return solver->make_term(true);
    }
    
    Term any_three = three_or_more[0];
    for (size_t i = 1; i < three_or_more.size(); i++) {
      any_three = solver->make_term(Or, any_three, three_or_more[i]);
    }
    return solver->make_term(Not, any_three);
  };
  
  // Transition constraint: if s0 is true at t0, then s1 must be true at t1
  Term transition = solver->make_term(Implies, state_t0[0], state_t1[1]);
  
  solver->push(1);
  solver->assert_formula(at_most_two(state_t0));
  solver->assert_formula(at_most_two(state_t1));
  solver->assert_formula(transition);
  
  // Initial condition: s0 is true at t0
  solver->assert_formula(state_t0[0]);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "State t0: ";
  int count_t0 = 0;
  for (int i = 0; i < 4; i++) {
    Term val = solver->get_value(state_t0[i]);
    if (val->to_int() == 1) {
      cout << "s" << i << " ";
      count_t0++;
    }
  }
  cout << endl;
  
  cout << "State t1: ";
  int count_t1 = 0;
  for (int i = 0; i < 4; i++) {
    Term val = solver->get_value(state_t1[i]);
    if (val->to_int() == 1) {
      cout << "s" << i << " ";
      count_t1++;
    }
  }
  cout << endl;
  
  assert(count_t0 <= 2);
  assert(count_t1 <= 2);
  
  solver->pop(1);
  
  cout << "Complex boolean invariants test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Complex Boolean Tests..." << endl;
    
    test_nested_boolean_operations();
    test_boolean_equivalence_checking();
    test_quantified_boolean_patterns();
    test_boolean_circuit_synthesis();
    test_boolean_satisfiability_phases();
    test_boolean_optimization_problem();
    test_complex_boolean_invariants();
    
    cout << "All STP Complex Boolean Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 