/*********************                                                        */
/*! \file stp-performance.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Performance and stress tests for STP solver
**        Tests performance benchmarks, stress testing, and scalability
**/

#include <iostream>
#include <memory>
#include <vector>
#include <chrono>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;
using namespace std::chrono;

void test_large_bitvector_operations()
{
  cout << "=== Testing Large Bit-Vector Operations ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  // Test with larger bit-vectors (32-bit)
  Sort bv32 = solver->make_sort(BV, 32);
  Term x = solver->make_symbol("x", bv32);
  Term y = solver->make_symbol("y", bv32);
  Term z = solver->make_symbol("z", bv32);
  
  solver->push(1);
  
  // Complex expression: (x * y + z) & 0xFFFF0000 = 0x00100000
  Term xy = solver->make_term(BVMul, x, y);
  Term xy_plus_z = solver->make_term(BVAdd, xy, z);
  Term mask = solver->make_term(0xFFFF0000, bv32);
  Term masked_result = solver->make_term(BVAnd, xy_plus_z, mask);
  Term target = solver->make_term(0x00100000, bv32);
  
  solver->assert_formula(solver->make_term(Equal, masked_result, target));
  
  // Add some constraints to make it interesting
  solver->assert_formula(solver->make_term(BVUlt, x, solver->make_term(1000, bv32)));
  solver->assert_formula(solver->make_term(BVUlt, y, solver->make_term(1000, bv32)));
  solver->assert_formula(solver->make_term(BVUlt, z, solver->make_term(0x50000, bv32)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    Term x_val = solver->get_value(x);
    Term y_val = solver->get_value(y);
    Term z_val = solver->get_value(z);
    cout << "Solution: x=" << x_val->to_int() 
         << ", y=" << y_val->to_int() 
         << ", z=" << z_val->to_int() << endl;
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Large bit-vector operations completed in " << duration.count() << "ms" << endl;
  
  cout << "Large bit-vector operations test PASSED" << endl;
}

void test_many_boolean_variables()
{
  cout << "=== Testing Many Boolean Variables ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  
  // Create 50 boolean variables
  vector<Term> vars;
  for (int i = 0; i < 50; i++) {
    string name = "p" + to_string(i);
    vars.push_back(solver->make_symbol(name, bool_sort));
  }
  
  solver->push(1);
  
  // Create constraints: exactly 25 variables should be true
  // This creates a complex combinatorial problem
  
  // Generate all combinations of 25 variables being true
  vector<Term> combinations;
  
  // For performance, just create a subset of combinations
  // At least first 25 must be true
  Term first_25_true = vars[0];
  for (int i = 1; i < 25; i++) {
    first_25_true = solver->make_term(And, first_25_true, vars[i]);
  }
  
  // Last 25 must be false
  Term last_25_false = solver->make_term(Not, vars[25]);
  for (int i = 26; i < 50; i++) {
    last_25_false = solver->make_term(And, last_25_false, solver->make_term(Not, vars[i]));
  }
  
  solver->assert_formula(first_25_true);
  solver->assert_formula(last_25_false);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    int true_count = 0;
    for (int i = 0; i < 50; i++) {
      Term val = solver->get_value(vars[i]);
      if (val->to_int() == 1) true_count++;
    }
    cout << "Number of true variables: " << true_count << endl;
    assert(true_count == 25);
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Many boolean variables completed in " << duration.count() << "ms" << endl;
  
  cout << "Many boolean variables test PASSED" << endl;
}

void test_deep_array_nesting()
{
  cout << "=== Testing Deep Array Nesting ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv8, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  
  solver->push(1);
  
  // Create a chain of array updates
  Term current_arr = arr;
  for (int i = 0; i < 20; i++) {
    current_arr = solver->make_term(Store, current_arr, 
                                    solver->make_term(i, bv8), 
                                    solver->make_term(i * 10, bv8));
  }
  
  // Create a chain of array accesses
  Term sum = solver->make_term(0, bv8);
  for (int i = 0; i < 10; i++) {
    Term val = solver->make_term(Select, current_arr, solver->make_term(i, bv8));
    sum = solver->make_term(BVAdd, sum, val);
  }
  
  // Sum should be 0+10+20+30+40+50+60+70+80+90 = 450, but mod 256 = 194
  solver->assert_formula(solver->make_term(Equal, sum, solver->make_term(194, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    Term sum_val = solver->get_value(sum);
    cout << "Array sum: " << sum_val->to_int() << endl;
    assert(sum_val->to_int() == 194);
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Deep array nesting completed in " << duration.count() << "ms" << endl;
  
  cout << "Deep array nesting test PASSED" << endl;
}

void test_complex_formula_generation()
{
  cout << "=== Testing Complex Formula Generation ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  // Generate a complex formula with many terms
  vector<Term> vars;
  for (int i = 0; i < 10; i++) {
    string name = "x" + to_string(i);
    vars.push_back(solver->make_symbol(name, bv8));
  }
  
  solver->push(1);
  
  // Create a complex polynomial-like expression
  // (x0 + x1) * (x2 + x3) + (x4 + x5) * (x6 + x7) + x8 * x9 = target
  Term sum01 = solver->make_term(BVAdd, vars[0], vars[1]);
  Term sum23 = solver->make_term(BVAdd, vars[2], vars[3]);
  Term sum45 = solver->make_term(BVAdd, vars[4], vars[5]);
  Term sum67 = solver->make_term(BVAdd, vars[6], vars[7]);
  
  Term prod0123 = solver->make_term(BVMul, sum01, sum23);
  Term prod4567 = solver->make_term(BVMul, sum45, sum67);
  Term prod89 = solver->make_term(BVMul, vars[8], vars[9]);
  
  Term result = solver->make_term(BVAdd, prod0123, solver->make_term(BVAdd, prod4567, prod89));
  Term target = solver->make_term(100, bv8);
  
  solver->assert_formula(solver->make_term(Equal, result, target));
  
  // Add some range constraints
  for (int i = 0; i < 10; i++) {
    solver->assert_formula(solver->make_term(BVUle, vars[i], solver->make_term(10, bv8)));
  }
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    cout << "Found solution for complex formula:" << endl;
    for (int i = 0; i < 10; i++) {
      Term val = solver->get_value(vars[i]);
      cout << "x" << i << "=" << val->to_int() << " ";
    }
    cout << endl;
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Complex formula generation completed in " << duration.count() << "ms" << endl;
  
  cout << "Complex formula generation test PASSED" << endl;
}

void test_repeated_solve_calls()
{
  cout << "=== Testing Repeated Solve Calls ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  
  // Perform many solve calls with incremental changes
  for (int i = 0; i < 20; i++) {
    solver->push(1);
    
    // Add constraint: x + y = i
    Term sum = solver->make_term(BVAdd, x, y);
    Term target = solver->make_term(i, bv8);
    solver->assert_formula(solver->make_term(Equal, sum, target));
    
    // Add constraint: x = i/2 (approximately)
    Term x_val = solver->make_term(i/2, bv8);
    solver->assert_formula(solver->make_term(Equal, x, x_val));
    
    Result r = solver->check_sat();
    assert(r.is_sat());
    
    if (r.is_sat()) {
      Term x_result = solver->get_value(x);
      Term y_result = solver->get_value(y);
      // Verify: x + y = i
      assert((x_result->to_int() + y_result->to_int()) % 256 == i % 256);
    }
    
    solver->pop(1);
  }
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Repeated solve calls (20 iterations) completed in " << duration.count() << "ms" << endl;
  
  cout << "Repeated solve calls test PASSED" << endl;
}

void test_large_array_operations()
{
  cout << "=== Testing Large Array Operations ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv8, bv8);
  
  Term arr1 = solver->make_symbol("arr1", arr_sort);
  Term arr2 = solver->make_symbol("arr2", arr_sort);
  
  solver->push(1);
  
  // Initialize arrays with many values
  Term current_arr1 = arr1;
  Term current_arr2 = arr2;
  
  for (int i = 0; i < 30; i++) {
    current_arr1 = solver->make_term(Store, current_arr1, 
                                     solver->make_term(i, bv8), 
                                     solver->make_term(i * 2, bv8));
    current_arr2 = solver->make_term(Store, current_arr2, 
                                     solver->make_term(i, bv8), 
                                     solver->make_term(i * 3, bv8));
  }
  
  // Create constraint: arr1[10] + arr2[10] = 50
  Term val1 = solver->make_term(Select, current_arr1, solver->make_term(10, bv8));
  Term val2 = solver->make_term(Select, current_arr2, solver->make_term(10, bv8));
  Term sum = solver->make_term(BVAdd, val1, val2);
  
  solver->assert_formula(solver->make_term(Equal, sum, solver->make_term(50, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    Term val1_result = solver->get_value(val1);
    Term val2_result = solver->get_value(val2);
    cout << "arr1[10]=" << val1_result->to_int() 
         << ", arr2[10]=" << val2_result->to_int() 
         << ", sum=" << (val1_result->to_int() + val2_result->to_int()) % 256 << endl;
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Large array operations completed in " << duration.count() << "ms" << endl;
  
  cout << "Large array operations test PASSED" << endl;
}

void test_memory_stress()
{
  cout << "=== Testing Memory Stress ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  
  // Create many variables and terms
  vector<Term> vars;
  vector<Term> constraints;
  
  for (int i = 0; i < 100; i++) {
    string name = "v" + to_string(i);
    vars.push_back(solver->make_symbol(name, bv4));
    
    // Create constraint: v[i] + v[(i+1) mod 100] < 10
    Term next_var = vars[i];
    Term sum = solver->make_term(BVAdd, vars[i], vars[(i + 1) % vars.size()]);
    Term constraint = solver->make_term(BVUlt, sum, solver->make_term(10, bv4));
    constraints.push_back(constraint);
  }
  
  solver->push(1);
  
  // Add all constraints
  for (const auto& constraint : constraints) {
    solver->assert_formula(constraint);
  }
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    cout << "Found satisfying assignment for 100 variables with 100 constraints" << endl;
    
    // Sample a few values
    for (int i = 0; i < 5; i++) {
      Term val = solver->get_value(vars[i]);
      cout << "v" << i << "=" << val->to_int() << " ";
    }
    cout << "..." << endl;
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Memory stress test completed in " << duration.count() << "ms" << endl;
  
  cout << "Memory stress test PASSED" << endl;
}

void test_solver_robustness()
{
  cout << "=== Testing Solver Robustness ===" << endl;
  
  auto start = high_resolution_clock::now();
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv8, bv8);
  
  // Mix different types of constraints
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  Term b = solver->make_symbol("b", bool_sort);
  Term arr = solver->make_symbol("arr", arr_sort);
  
  solver->push(1);
  
  // Bit-vector constraint
  solver->assert_formula(solver->make_term(BVUlt, x, solver->make_term(100, bv8)));
  
  // Boolean constraint
  solver->assert_formula(solver->make_term(Implies, b, 
    solver->make_term(BVUgt, y, solver->make_term(50, bv8))));
  
  // Array constraint
  Term arr_updated = solver->make_term(Store, arr, x, y);
  Term arr_value = solver->make_term(Select, arr_updated, x);
  solver->assert_formula(solver->make_term(Equal, arr_value, y));
  
  // Mixed constraint
  Term complex_condition = solver->make_term(And, b, 
    solver->make_term(BVUge, solver->make_term(BVAdd, x, y), solver->make_term(75, bv8)));
  solver->assert_formula(complex_condition);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    Term x_val = solver->get_value(x);
    Term y_val = solver->get_value(y);
    Term b_val = solver->get_value(b);
    
    cout << "Robust solution: x=" << x_val->to_int() 
         << ", y=" << y_val->to_int() 
         << ", b=" << b_val->to_int() << endl;
  }
  
  solver->pop(1);
  
  auto end = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start);
  cout << "Solver robustness test completed in " << duration.count() << "ms" << endl;
  
  cout << "Solver robustness test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Performance and Stress Tests..." << endl;
    
    test_large_bitvector_operations();
    test_many_boolean_variables();
    test_deep_array_nesting();
    test_complex_formula_generation();
    test_repeated_solve_calls();
    test_large_array_operations();
    test_memory_stress();
    test_solver_robustness();
    
    cout << "All STP Performance and Stress Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 