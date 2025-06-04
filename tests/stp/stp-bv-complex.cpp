/*********************                                                        */
/*! \file stp-bv-complex.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Complex bit-vector tests for STP solver
**        Tests advanced operations, overflow/underflow, signed ops, edge cases
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_bv_overflow_underflow()
{
  cout << "=== Testing BV Overflow and Underflow ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4); // 4-bit values: 0-15
  
  // Test overflow: 15 + 1 = 0 (in 4-bit arithmetic)
  Term max_val = solver->make_term(15, bv4); // 1111
  Term one = solver->make_term(1, bv4);      // 0001
  Term zero = solver->make_term(0, bv4);     // 0000
  
  solver->push(1);
  Term overflow_result = solver->make_term(BVAdd, max_val, one);
  solver->assert_formula(solver->make_term(Equal, overflow_result, zero));
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term result_val = solver->get_value(overflow_result);
  assert(result_val->to_int() == 0);
  solver->pop(1);
  
  // Test underflow: 0 - 1 = 15 (in 4-bit arithmetic)
  solver->push(1);
  Term underflow_result = solver->make_term(BVSub, zero, one);
  solver->assert_formula(solver->make_term(Equal, underflow_result, max_val));
  r = solver->check_sat();
  assert(r.is_sat());
  
  result_val = solver->get_value(underflow_result);
  assert(result_val->to_int() == 15);
  solver->pop(1);
  
  cout << "BV overflow and underflow test PASSED" << endl;
}

void test_bv_signed_operations()
{
  cout << "=== Testing BV Signed Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  
  // In 4-bit two's complement: -1 = 1111, -2 = 1110, etc.
  Term neg_one = solver->make_term("1111", bv4, 2); // -1 in two's complement
  Term neg_two = solver->make_term("1110", bv4, 2); // -2 in two's complement
  Term pos_one = solver->make_term(1, bv4);         // 1
  Term pos_two = solver->make_term(2, bv4);         // 2
  
  // Test signed less than: -2 < -1
  solver->push(1);
  solver->assert_formula(solver->make_term(BVSlt, neg_two, neg_one));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test signed less than: -1 < 1
  solver->push(1);
  solver->assert_formula(solver->make_term(BVSlt, neg_one, pos_one));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test unsigned vs signed comparison: 15 > 1 (unsigned) but -1 < 1 (signed)
  solver->push(1);
  solver->assert_formula(solver->make_term(BVUgt, neg_one, pos_one)); // 15 > 1 unsigned
  solver->assert_formula(solver->make_term(BVSlt, neg_one, pos_one)); // -1 < 1 signed
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test signed division: -4 / 2 = -2
  Sort bv8 = solver->make_sort(BV, 8);
  Term neg_four = solver->make_term("11111100", bv8, 2); // -4 in 8-bit two's complement
  Term two_8bit = solver->make_term(2, bv8);
  Term neg_two_8bit = solver->make_term("11111110", bv8, 2); // -2 in 8-bit two's complement
  
  solver->push(1);
  Term sdiv_result = solver->make_term(BVSdiv, neg_four, two_8bit);
  solver->assert_formula(solver->make_term(Equal, sdiv_result, neg_two_8bit));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV signed operations test PASSED" << endl;
}

void test_bv_advanced_bitwise()
{
  cout << "=== Testing Advanced BV Bitwise Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  // Test NAND: ~(a & b) 
  Term a = solver->make_term("11001100", bv8, 2); // 204
  Term b = solver->make_term("10101010", bv8, 2); // 170
  Term expected_nand = solver->make_term("01110111", bv8, 2); // ~(204 & 170)
  
  solver->push(1);
  Term nand_result = solver->make_term(BVNand, a, b);
  solver->assert_formula(solver->make_term(Equal, nand_result, expected_nand));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test NOR: ~(a | b)
  Term expected_nor = solver->make_term("00010001", bv8, 2); // ~(204 | 170)
  
  solver->push(1);
  Term nor_result = solver->make_term(BVNor, a, b);
  solver->assert_formula(solver->make_term(Equal, nor_result, expected_nor));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test XNOR: ~(a ^ b)
  Term expected_xnor = solver->make_term("10011001", bv8, 2); // ~(204 ^ 170)
  
  solver->push(1);
  Term xnor_result = solver->make_term(BVXnor, a, b);
  solver->assert_formula(solver->make_term(Equal, xnor_result, expected_xnor));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "Advanced BV bitwise operations test PASSED" << endl;
}

void test_bv_division_and_modulo()
{
  cout << "=== Testing BV Division and Modulo Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  // Test unsigned division: 20 / 3 = 6
  Term twenty = solver->make_term(20, bv8);
  Term three = solver->make_term(3, bv8);
  Term six = solver->make_term(6, bv8);
  
  solver->push(1);
  Term udiv_result = solver->make_term(BVUdiv, twenty, three);
  solver->assert_formula(solver->make_term(Equal, udiv_result, six));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test unsigned remainder: 20 % 3 = 2
  Term two = solver->make_term(2, bv8);
  
  solver->push(1);
  Term urem_result = solver->make_term(BVUrem, twenty, three);
  solver->assert_formula(solver->make_term(Equal, urem_result, two));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test signed remainder: -20 % 3 = -2
  Term neg_twenty = solver->make_term(-20, bv8);
  Term neg_two = solver->make_term(-2, bv8);
  
  solver->push(1);
  Term srem_result = solver->make_term(BVSrem, neg_twenty, three);
  solver->assert_formula(solver->make_term(Equal, srem_result, neg_two));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test signed modulo: -20 mod 3 = 1 (differs from remainder)
  Term one = solver->make_term(1, bv8);
  
  solver->push(1);
  Term smod_result = solver->make_term(BVSmod, neg_twenty, three);
  solver->assert_formula(solver->make_term(Equal, smod_result, one));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV division and modulo test PASSED" << endl;
}

void test_bv_shift_edge_cases()
{
  cout << "=== Testing BV Shift Edge Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  Term val = solver->make_term("10110011", bv8, 2); // 179
  Term zero = solver->make_term(0, bv8);
  Term eight = solver->make_term(8, bv8);
  
  // Test shift by 0 (should be identity)
  solver->push(1);
  Term lshift_0 = solver->make_term(BVShl, val, zero);
  solver->assert_formula(solver->make_term(Equal, lshift_0, val));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test shift by width (should be 0 for left shift)
  solver->push(1);
  Term lshift_8 = solver->make_term(BVShl, val, eight);
  solver->assert_formula(solver->make_term(Equal, lshift_8, zero));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test arithmetic right shift with negative number
  Term neg_val = solver->make_term("10000001", bv8, 2); // -127 in two's complement
  Term one = solver->make_term(1, bv8);
  Term expected_ashr = solver->make_term("11000000", bv8, 2); // Sign extended
  
  solver->push(1);
  Term ashr_result = solver->make_term(BVAshr, neg_val, one);
  solver->assert_formula(solver->make_term(Equal, ashr_result, expected_ashr));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV shift edge cases test PASSED" << endl;
}

void test_bv_complex_extract_concat()
{
  cout << "=== Testing Complex BV Extract and Concat ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv16 = solver->make_sort(BV, 16);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bv4 = solver->make_sort(BV, 4);
  
  Term val16 = solver->make_term("1100110010101010", bv16, 2); // 52650
  
  // Extract high and low bytes
  Op extract_high(Extract, 15, 8);
  Op extract_low(Extract, 7, 0);
  Term high_byte = solver->make_term(extract_high, val16);
  Term low_byte = solver->make_term(extract_low, val16);
  
  // Verify extract results
  Term expected_high = solver->make_term("11001100", bv8, 2); // 204
  Term expected_low = solver->make_term("10101010", bv8, 2);  // 170
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, high_byte, expected_high));
  solver->assert_formula(solver->make_term(Equal, low_byte, expected_low));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Reconstruct original value by concatenation
  solver->push(1);
  Term reconstructed = solver->make_term(Concat, high_byte, low_byte);
  solver->assert_formula(solver->make_term(Equal, reconstructed, val16));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test multiple extract and concat operations
  Op extract_3_0(Extract, 3, 0);
  Op extract_7_4(Extract, 7, 4);
  Op extract_11_8(Extract, 11, 8);
  Op extract_15_12(Extract, 15, 12);
  
  Term nibble0 = solver->make_term(extract_3_0, val16);
  Term nibble1 = solver->make_term(extract_7_4, val16);
  Term nibble2 = solver->make_term(extract_11_8, val16);
  Term nibble3 = solver->make_term(extract_15_12, val16);
  
  // Reconstruct from nibbles
  solver->push(1);
  Term concat1 = solver->make_term(Concat, nibble1, nibble0);
  Term concat2 = solver->make_term(Concat, nibble3, nibble2);
  Term final_concat = solver->make_term(Concat, concat2, concat1);
  solver->assert_formula(solver->make_term(Equal, final_concat, val16));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "Complex BV extract and concat test PASSED" << endl;
}

void test_bv_multiplication_edge_cases()
{
  cout << "=== Testing BV Multiplication Edge Cases ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  
  // Test multiplication overflow: 16 * 16 = 256 = 0 (in 8-bit)
  Term sixteen = solver->make_term(16, bv8);
  Term zero = solver->make_term(0, bv8);
  
  solver->push(1);
  Term mul_overflow = solver->make_term(BVMul, sixteen, sixteen);
  solver->assert_formula(solver->make_term(Equal, mul_overflow, zero));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test multiplication by 0
  Term five = solver->make_term(5, bv8);
  
  solver->push(1);
  Term mul_by_zero = solver->make_term(BVMul, five, zero);
  solver->assert_formula(solver->make_term(Equal, mul_by_zero, zero));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test multiplication by 1 (identity)
  Term one = solver->make_term(1, bv8);
  
  solver->push(1);
  Term mul_by_one = solver->make_term(BVMul, five, one);
  solver->assert_formula(solver->make_term(Equal, mul_by_one, five));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "BV multiplication edge cases test PASSED" << endl;
}

void test_bv_complex_constraints()
{
  cout << "=== Testing Complex BV Constraints ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  Term z = solver->make_symbol("z", bv8);
  
  // Complex constraint: (x + y) * z = x * z + y * z (distributive law)
  solver->push(1);
  Term sum_xy = solver->make_term(BVAdd, x, y);
  Term left_side = solver->make_term(BVMul, sum_xy, z);
  
  Term xz = solver->make_term(BVMul, x, z);
  Term yz = solver->make_term(BVMul, y, z);
  Term right_side = solver->make_term(BVAdd, xz, yz);
  
  solver->assert_formula(solver->make_term(Equal, left_side, right_side));
  
  // Add some specific constraints to make it interesting
  Term fifty = solver->make_term(50, bv8);
  Term thirty = solver->make_term(30, bv8);
  Term two = solver->make_term(2, bv8);
  
  solver->assert_formula(solver->make_term(BVUlt, x, fifty));
  solver->assert_formula(solver->make_term(BVUlt, y, thirty));
  solver->assert_formula(solver->make_term(Equal, z, two));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Get values and verify
  Term x_val = solver->get_value(x);
  Term y_val = solver->get_value(y);
  Term z_val = solver->get_value(z);
  
  cout << "x = " << x_val->to_int() << ", y = " << y_val->to_int() 
       << ", z = " << z_val->to_int() << endl;
  
  assert(x_val->to_int() < 50);
  assert(y_val->to_int() < 30);
  assert(z_val->to_int() == 2);
  
  solver->pop(1);
  
  cout << "Complex BV constraints test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Complex Bit-Vector Tests..." << endl;
    
    test_bv_overflow_underflow();
    test_bv_signed_operations();
    test_bv_advanced_bitwise();
    test_bv_division_and_modulo();
    test_bv_shift_edge_cases();
    test_bv_complex_extract_concat();
    test_bv_multiplication_edge_cases();
    test_bv_complex_constraints();
    
    cout << "All STP Complex Bit-Vector Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 