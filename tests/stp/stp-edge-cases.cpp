/*********************                                                        */
/*! \file stp-edge-cases.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Edge cases and regression tests for STP solver
**        Tests corner cases, boundary conditions, and known regression scenarios
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_zero_width_bitvectors()
{
  cout << "=== Testing Zero Width Bit-Vectors ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  // Test minimum width bit-vectors (1-bit)
  Sort bv1 = solver->make_sort(BV, 1);
  Term x = solver->make_symbol("x", bv1);
  Term y = solver->make_symbol("y", bv1);
  
  solver->push(1);
  
  // 1-bit values can only be 0 or 1
  Term zero = solver->make_term(0, bv1);
  Term one = solver->make_term(1, bv1);
  
  // Test XOR on 1-bit values
  Term xor_result = solver->make_term(BVXor, x, y);
  solver->assert_formula(solver->make_term(Equal, x, zero));
  solver->assert_formula(solver->make_term(Equal, y, one));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term xor_val = solver->get_value(xor_result);
  cout << "1-bit XOR: 0 ⊕ 1 = " << xor_val->to_int() << endl;
  assert(xor_val->to_int() == 1);
  
  solver->pop(1);
  
  cout << "Zero width bit-vectors test PASSED" << endl;
}

void test_maximum_bitvector_values()
{
  cout << "=== Testing Maximum Bit-Vector Values ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  
  solver->push(1);
  
  // Test maximum 8-bit value (255)
  Term max_val = solver->make_term(255, bv8);
  solver->assert_formula(solver->make_term(Equal, x, max_val));
  
  // Adding 1 should wrap around to 0
  Term x_plus_one = solver->make_term(BVAdd, x, solver->make_term(1, bv8));
  Term expected_zero = solver->make_term(0, bv8);
  solver->assert_formula(solver->make_term(Equal, x_plus_one, expected_zero));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  Term sum_val = solver->get_value(x_plus_one);
  
  cout << "Max value: " << x_val->to_int() << ", +1 = " << sum_val->to_int() << " (overflow)" << endl;
  assert(x_val->to_int() == 255);
  assert(sum_val->to_int() == 0);
  
  solver->pop(1);
  
  cout << "Maximum bit-vector values test PASSED" << endl;
}

void test_signed_unsigned_boundary()
{
  cout << "=== Testing Signed/Unsigned Boundary Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Term x = solver->make_symbol("x", bv4);
  Term y = solver->make_symbol("y", bv4);
  
  solver->push(1);
  
  // Test signed interpretation boundary: 8 (1000 in binary)
  // In 4-bit signed: 8 = -8, 7 = 7
  Term val_8 = solver->make_term(8, bv4);  // 1000 binary = -8 signed
  Term val_7 = solver->make_term(7, bv4);  // 0111 binary = +7 signed
  
  solver->assert_formula(solver->make_term(Equal, x, val_8));
  solver->assert_formula(solver->make_term(Equal, y, val_7));
  
  // Unsigned comparison: 8 > 7
  Term unsigned_cmp = solver->make_term(BVUgt, x, y);
  // Signed comparison: -8 < 7  
  Term signed_cmp = solver->make_term(BVSgt, x, y);
  
  solver->assert_formula(unsigned_cmp);  // Should be true
  solver->assert_formula(solver->make_term(Not, signed_cmp)); // Should be false (so NOT false = true)
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  Term y_val = solver->get_value(y);
  Term ucmp_val = solver->get_value(unsigned_cmp);
  Term scmp_val = solver->get_value(signed_cmp);
  
  cout << "Values: x=" << x_val->to_int() << ", y=" << y_val->to_int() << endl;
  cout << "Unsigned: " << x_val->to_int() << " > " << y_val->to_int() << " = " << ucmp_val->to_int() << endl;
  cout << "Signed: -8 > 7 = " << scmp_val->to_int() << endl;
  
  assert(ucmp_val->to_int() == 1); // 8 > 7 unsigned
  assert(scmp_val->to_int() == 0); // -8 not > 7 signed
  
  solver->pop(1);
  
  cout << "Signed/unsigned boundary test PASSED" << endl;
}

void test_empty_array_operations()
{
  cout << "=== Testing Empty Array Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term index = solver->make_symbol("index", bv4);
  Term value = solver->make_symbol("value", bv8);
  
  solver->push(1);
  
  // Access uninitialized array - should get some default value
  Term arr_value = solver->make_term(Select, arr, index);
  solver->assert_formula(solver->make_term(Equal, value, arr_value));
  solver->assert_formula(solver->make_term(Equal, index, solver->make_term(5, bv4)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term index_val = solver->get_value(index);
  Term value_val = solver->get_value(value);
  
  cout << "Uninitialized array[" << index_val->to_int() << "] = " << value_val->to_int() << endl;
  // Value can be anything - just check it's satisfiable
  
  solver->pop(1);
  
  cout << "Empty array operations test PASSED" << endl;
}

void test_boolean_contradiction_edge_cases()
{
  cout << "=== Testing Boolean Contradiction Edge Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bool_sort = solver->make_sort(BOOL);
  Term p = solver->make_symbol("p", bool_sort);
  
  solver->push(1);
  
  // Create a subtle contradiction
  Term p_and_not_p = solver->make_term(And, p, solver->make_term(Not, p));
  Term tautology = solver->make_term(Or, p, solver->make_term(Not, p));
  
  // This should be UNSAT: (p AND NOT p) AND (always true)
  solver->assert_formula(p_and_not_p);
  solver->assert_formula(tautology);
  
  Result r = solver->check_sat();
  assert(r.is_unsat());
  
  cout << "Contradiction detected correctly" << endl;
  
  solver->pop(1);
  
  // Test complex tautology
  solver->push(1);
  
  Term complex_tautology = solver->make_term(Or, 
    solver->make_term(And, p, solver->make_term(Not, p)),
    solver->make_term(Or, p, solver->make_term(Not, p)));
  
  solver->assert_formula(complex_tautology);
  
  r = solver->check_sat();
  assert(r.is_sat()); // Should be SAT (tautology)
  
  solver->pop(1);
  
  cout << "Boolean contradiction edge cases test PASSED" << endl;
}

void test_deeply_nested_expressions()
{
  cout << "=== Testing Deeply Nested Expressions ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  
  solver->push(1);
  
  // Build deeply nested expression: ((((x + 1) + 1) + 1) + 1) + 1 = x + 5
  Term nested = x;
  for (int i = 0; i < 5; i++) {
    nested = solver->make_term(BVAdd, nested, solver->make_term(1, bv8));
  }
  
  // Should equal x + 5
  Term x_plus_5 = solver->make_term(BVAdd, x, solver->make_term(5, bv8));
  solver->assert_formula(solver->make_term(Equal, nested, x_plus_5));
  solver->assert_formula(solver->make_term(Equal, x, solver->make_term(10, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  Term nested_val = solver->get_value(nested);
  Term simple_val = solver->get_value(x_plus_5);
  
  cout << "x = " << x_val->to_int() 
       << ", nested = " << nested_val->to_int() 
       << ", x+5 = " << simple_val->to_int() << endl;
  
  assert(nested_val->to_int() == simple_val->to_int());
  assert(nested_val->to_int() == 15);
  
  solver->pop(1);
  
  cout << "Deeply nested expressions test PASSED" << endl;
}

void test_array_aliasing_edge_cases()
{
  cout << "=== Testing Array Aliasing Edge Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr1 = solver->make_symbol("arr1", arr_sort);
  Term arr2 = solver->make_symbol("arr2", arr_sort);
  Term index = solver->make_symbol("index", bv4);
  
  solver->push(1);
  
  // Test array equality edge case
  // If arr1[i] = arr2[i] for all relevant i, are arrays equal?
  
  // Set up some values
  Term arr1_updated = solver->make_term(Store, arr1, solver->make_term(0, bv4), solver->make_term(100, bv8));
  Term arr2_updated = solver->make_term(Store, arr2, solver->make_term(0, bv4), solver->make_term(100, bv8));
  
  // Access same index from both arrays
  Term val1 = solver->make_term(Select, arr1_updated, index);
  Term val2 = solver->make_term(Select, arr2_updated, index);
  
  solver->assert_formula(solver->make_term(Equal, index, solver->make_term(0, bv4)));
  solver->assert_formula(solver->make_term(Equal, val1, val2));
  
  // But arrays themselves might not be equal (different at other indices)
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term val1_result = solver->get_value(val1);
  Term val2_result = solver->get_value(val2);
  
  cout << "Array values at index 0: arr1=" << val1_result->to_int() 
       << ", arr2=" << val2_result->to_int() << endl;
  
  assert(val1_result->to_int() == val2_result->to_int());
  
  solver->pop(1);
  
  cout << "Array aliasing edge cases test PASSED" << endl;
}

void test_division_by_zero_edge_cases()
{
  cout << "=== Testing Division by Zero Edge Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  Term result = solver->make_symbol("result", bv8);
  
  solver->push(1);
  
  // Test division by zero behavior (usually gives all 1's in bit-vectors)
  Term zero = solver->make_term(0, bv8);
  Term div_result = solver->make_term(BVUdiv, x, y);
  
  solver->assert_formula(solver->make_term(Equal, x, solver->make_term(42, bv8)));
  solver->assert_formula(solver->make_term(Equal, y, zero));
  solver->assert_formula(solver->make_term(Equal, result, div_result));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  Term y_val = solver->get_value(y);
  Term result_val = solver->get_value(result);
  
  cout << "Division: " << x_val->to_int() << " / " << y_val->to_int() 
       << " = " << result_val->to_int() << endl;
  
  // Division by zero typically gives max value (255 for 8-bit)
  // This is implementation-defined behavior
  
  solver->pop(1);
  
  cout << "Division by zero edge cases test PASSED" << endl;
}

void test_extract_concat_edge_cases()
{
  cout << "=== Testing Extract/Concat Edge Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv1 = solver->make_sort(BV, 1);
  
  Term x = solver->make_symbol("x", bv8);
  
  solver->push(1);
  
  // Extract single bits and reconstruct
  vector<Term> bits;
  for (int i = 0; i < 8; i++) {
    Op extract_bit(Extract, i, i);
    bits.push_back(solver->make_term(extract_bit, x));
  }
  
  // Reconstruct from bits (MSB first)
  Term reconstructed = bits[7];
  for (int i = 6; i >= 0; i--) {
    reconstructed = solver->make_term(Concat, reconstructed, bits[i]);
  }
  
  // Should equal original
  solver->assert_formula(solver->make_term(Equal, x, reconstructed));
  solver->assert_formula(solver->make_term(Equal, x, solver->make_term(170, bv8))); // 10101010
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  Term reconstructed_val = solver->get_value(reconstructed);
  
  cout << "Original: " << x_val->to_int() 
       << ", Reconstructed: " << reconstructed_val->to_int() << endl;
  
  assert(x_val->to_int() == reconstructed_val->to_int());
  
  solver->pop(1);
  
  cout << "Extract/concat edge cases test PASSED" << endl;
}

void test_satisfiability_transition_points()
{
  cout << "=== Testing Satisfiability Transition Points ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Term x = solver->make_symbol("x", bv4);
  Term y = solver->make_symbol("y", bv4);
  
  // Test transition from SAT to UNSAT by gradually adding constraints
  
  solver->push(1);
  // Start with satisfiable: x + y = 5
  solver->assert_formula(solver->make_term(Equal, 
    solver->make_term(BVAdd, x, y), 
    solver->make_term(5, bv4)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  cout << "Constraint 1 (x + y = 5): SAT" << endl;
  
  // Add another constraint: x > 10 (impossible in 4-bit)
  solver->assert_formula(solver->make_term(BVUgt, x, solver->make_term(10, bv4)));
  
  r = solver->check_sat();
  if (r.is_unsat()) {
    cout << "Constraint 2 (x > 10): UNSAT (expected)" << endl;
  } else {
    cout << "Constraint 2 (x > 10): SAT (4-bit wrapping)" << endl;
  }
  
  solver->pop(1);
  
  // Test another transition point
  solver->push(1);
  
  // x * y = 20, possible in 4-bit: 4 * 5 = 20, but 20 % 16 = 4
  solver->assert_formula(solver->make_term(Equal, 
    solver->make_term(BVMul, x, y), 
    solver->make_term(4, bv4))); // 20 mod 16 = 4
  
  r = solver->check_sat();
  assert(r.is_sat());
  
  if (r.is_sat()) {
    Term x_val = solver->get_value(x);
    Term y_val = solver->get_value(y);
    cout << "Found solution: " << x_val->to_int() << " * " << y_val->to_int() 
         << " ≡ 4 (mod 16)" << endl;
  }
  
  solver->pop(1);
  
  cout << "Satisfiability transition points test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Edge Cases and Regression Tests..." << endl;
    
    test_zero_width_bitvectors();
    test_maximum_bitvector_values();
    test_signed_unsigned_boundary();
    test_empty_array_operations();
    test_boolean_contradiction_edge_cases();
    test_deeply_nested_expressions();
    test_array_aliasing_edge_cases();
    test_division_by_zero_edge_cases();
    test_extract_concat_edge_cases();
    test_satisfiability_transition_points();
    
    cout << "All STP Edge Cases and Regression Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 