/*********************                                                        */
/*! \file stp-basic-bv.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Basic bit-vector tests for STP solver
**        Tests fundamental bit-vector operations, constants, and constraints
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_bv_sorts_and_constants()
{
  cout << "=== Testing BV Sorts and Constants ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  // Test different bit-vector widths
  Sort bv1 = solver->make_sort(BV, 1);
  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bv16 = solver->make_sort(BV, 16);
  Sort bv32 = solver->make_sort(BV, 32);
  
  assert(bv1 != bv4);
  assert(bv4 != bv8);
  assert(bv8 != bv16);
  assert(bv16 != bv32);
  
  // Test bit-vector constants with different representations
  Term zero4 = solver->make_term(0, bv4);
  Term one4 = solver->make_term(1, bv4);
  Term fifteen4 = solver->make_term(15, bv4);
  
  // Test binary representation
  Term bin_fifteen = solver->make_term("1111", bv4, 2);
  
  // Test hexadecimal representation  
  Term hex_fifteen = solver->make_term("F", bv4, 16);
  
  // Test that different representations of same value are equivalent
  solver->push(1);
  Term eq1 = solver->make_term(Equal, fifteen4, bin_fifteen);
  Term eq2 = solver->make_term(Equal, fifteen4, hex_fifteen);
  solver->assert_formula(eq1);
  solver->assert_formula(eq2);
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV sorts and constants test PASSED" << endl;
}

void test_bv_variables()
{
  cout << "=== Testing BV Variables ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  // Create bit-vector variables
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  Term z = solver->make_symbol("z", bv8);
  
  // Test that variables are distinct
  assert(x != y);
  assert(y != z);
  assert(x != z);
  
  // Test variable assignment
  solver->push(1);
  Term val42 = solver->make_term(42, bv8);
  solver->assert_formula(solver->make_term(Equal, x, val42));
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  assert(x_val->to_int() == 42);
  solver->pop(1);
  
  cout << "BV variables test PASSED" << endl;
}

void test_bv_arithmetic()
{
  cout << "=== Testing BV Arithmetic Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  
  // Test addition
  Term five = solver->make_term(5, bv8);
  Term three = solver->make_term(3, bv8);
  Term eight = solver->make_term(8, bv8);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, x, five));
  solver->assert_formula(solver->make_term(Equal, y, three));
  Term sum = solver->make_term(BVAdd, x, y);
  solver->assert_formula(solver->make_term(Equal, sum, eight));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test subtraction
  solver->push(1);
  Term ten = solver->make_term(10, bv8);
  Term four = solver->make_term(4, bv8);
  Term six = solver->make_term(6, bv8);
  solver->assert_formula(solver->make_term(Equal, x, ten));
  solver->assert_formula(solver->make_term(Equal, y, four));
  Term diff = solver->make_term(BVSub, x, y);
  solver->assert_formula(solver->make_term(Equal, diff, six));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test multiplication
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, x, three));
  solver->assert_formula(solver->make_term(Equal, y, four));
  Term twelve = solver->make_term(12, bv8);
  Term prod = solver->make_term(BVMul, x, y);
  solver->assert_formula(solver->make_term(Equal, prod, twelve));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV arithmetic test PASSED" << endl;
}

void test_bv_bitwise_operations()
{
  cout << "=== Testing BV Bitwise Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  
  // Test AND operation: 1100 & 1010 = 1000
  Term val12 = solver->make_term("1100", bv4, 2); // 12
  Term val10 = solver->make_term("1010", bv4, 2); // 10
  Term val8 = solver->make_term("1000", bv4, 2);  // 8
  
  solver->push(1);
  Term and_result = solver->make_term(BVAnd, val12, val10);
  solver->assert_formula(solver->make_term(Equal, and_result, val8));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test OR operation: 1100 | 1010 = 1110
  Term val14 = solver->make_term("1110", bv4, 2); // 14
  
  solver->push(1);
  Term or_result = solver->make_term(BVOr, val12, val10);
  solver->assert_formula(solver->make_term(Equal, or_result, val14));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test XOR operation: 1100 ^ 1010 = 0110
  Term val6 = solver->make_term("0110", bv4, 2); // 6
  
  solver->push(1);
  Term xor_result = solver->make_term(BVXor, val12, val10);
  solver->assert_formula(solver->make_term(Equal, xor_result, val6));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test NOT operation: ~1100 = 0011
  Term val3 = solver->make_term("0011", bv4, 2); // 3
  
  solver->push(1);
  Term not_result = solver->make_term(BVNot, val12);
  solver->assert_formula(solver->make_term(Equal, not_result, val3));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV bitwise operations test PASSED" << endl;
}

void test_bv_comparison_operations()
{
  cout << "=== Testing BV Comparison Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  
  Term ten = solver->make_term(10, bv8);
  Term five = solver->make_term(5, bv8);
  
  // Test unsigned less than
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, x, five));
  solver->assert_formula(solver->make_term(Equal, y, ten));
  solver->assert_formula(solver->make_term(BVUlt, x, y));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test unsigned greater than or equal
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, x, ten));
  solver->assert_formula(solver->make_term(Equal, y, five));
  solver->assert_formula(solver->make_term(BVUge, x, y));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test equality
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, x, ten));
  solver->assert_formula(solver->make_term(Equal, y, ten));
  solver->assert_formula(solver->make_term(Equal, x, y));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV comparison operations test PASSED" << endl;
}

void test_bv_shift_operations()
{
  cout << "=== Testing BV Shift Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  // Test left shift: 5 << 1 = 10
  Term five = solver->make_term(5, bv8);
  Term one = solver->make_term(1, bv8);
  Term ten = solver->make_term(10, bv8);
  
  solver->push(1);
  Term lshift_result = solver->make_term(BVShl, five, one);
  solver->assert_formula(solver->make_term(Equal, lshift_result, ten));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test logical right shift: 10 >> 1 = 5
  solver->push(1);
  Term rshift_result = solver->make_term(BVLshr, ten, one);
  solver->assert_formula(solver->make_term(Equal, rshift_result, five));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV shift operations test PASSED" << endl;
}

void test_bv_extract_concat()
{
  cout << "=== Testing BV Extract and Concat Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort bv4 = solver->make_sort(BV, 4);
  
  // Test extract: extract bits [7:4] from 11110000 = 1111
  Term val240 = solver->make_term("11110000", bv8, 2); // 240
  Term val15 = solver->make_term("1111", bv4, 2); // 15
  
  solver->push(1);
  Op extract_op(Extract, 7, 4);
  Term extract_result = solver->make_term(extract_op, val240);
  solver->assert_formula(solver->make_term(Equal, extract_result, val15));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test concat: concatenate 1111 and 0000 = 11110000
  Term val0 = solver->make_term("0000", bv4, 2); // 0
  
  solver->push(1);
  Term concat_result = solver->make_term(Concat, val15, val0);
  solver->assert_formula(solver->make_term(Equal, concat_result, val240));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV extract and concat test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Basic Bit-Vector Tests..." << endl;
    
    test_bv_sorts_and_constants();
    test_bv_variables();
    test_bv_arithmetic();
    test_bv_bitwise_operations();
    test_bv_comparison_operations();
    test_bv_shift_operations();
    test_bv_extract_concat();
    
    cout << "All STP Basic Bit-Vector Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 