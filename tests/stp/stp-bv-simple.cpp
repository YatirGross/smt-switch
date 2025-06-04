/*********************                                                        */
/*! \file stp-bv-simple.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Simple bit-vector tests for STP solver
**        Tests practical bit-vector constraints and common use cases
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_simple_arithmetic_constraints()
{
  cout << "=== Testing Simple Arithmetic Constraints ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  Term y = solver->make_symbol("y", bv8);
  
  // Simple constraint: x + y = 15, x < 10, y > 5
  Term fifteen = solver->make_term(15, bv8);
  Term ten = solver->make_term(10, bv8);
  Term five = solver->make_term(5, bv8);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, solver->make_term(BVAdd, x, y), fifteen));
  solver->assert_formula(solver->make_term(BVUlt, x, ten));
  solver->assert_formula(solver->make_term(BVUgt, y, five));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  Term y_val = solver->get_value(y);
  
  cout << "Solution: x=" << x_val->to_int() << ", y=" << y_val->to_int() << endl;
  
  // Verify constraints
  assert(x_val->to_int() + y_val->to_int() == 15);
  assert(x_val->to_int() < 10);
  assert(y_val->to_int() > 5);
  
  solver->pop(1);
  
  cout << "Simple arithmetic constraints test PASSED" << endl;
}

void test_range_constraints()
{
  cout << "=== Testing Range Constraints ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term value = solver->make_symbol("value", bv8);
  
  // Value must be in range [50, 100]
  Term min_val = solver->make_term(50, bv8);
  Term max_val = solver->make_term(100, bv8);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(BVUge, value, min_val));
  solver->assert_formula(solver->make_term(BVUle, value, max_val));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term value_val = solver->get_value(value);
  cout << "Value in range: " << value_val->to_int() << endl;
  
  assert(value_val->to_int() >= 50);
  assert(value_val->to_int() <= 100);
  
  solver->pop(1);
  
  cout << "Range constraints test PASSED" << endl;
}

void test_bit_manipulation()
{
  cout << "=== Testing Bit Manipulation ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term value = solver->make_symbol("value", bv8);
  
  // Set specific bits: bit 0 and bit 2 should be 1, bit 1 should be 0
  Term one = solver->make_term(1, bv8);
  Term two = solver->make_term(2, bv8);
  Term four = solver->make_term(4, bv8);
  
  // Extract individual bits
  Op extract_bit0(Extract, 0, 0);
  Op extract_bit1(Extract, 1, 1);
  Op extract_bit2(Extract, 2, 2);
  
  Term bit0 = solver->make_term(extract_bit0, value);
  Term bit1 = solver->make_term(extract_bit1, value);
  Term bit2 = solver->make_term(extract_bit2, value);
  
  Sort bv1 = solver->make_sort(BV, 1);
  Term one_bit = solver->make_term(1, bv1);
  Term zero_bit = solver->make_term(0, bv1);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, bit0, one_bit));   // bit 0 = 1
  solver->assert_formula(solver->make_term(Equal, bit1, zero_bit));  // bit 1 = 0
  solver->assert_formula(solver->make_term(Equal, bit2, one_bit));   // bit 2 = 1
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term value_val = solver->get_value(value);
  cout << "Value with specific bits: " << value_val->to_int() << endl;
  
  // Verify bits: should have pattern ...00101 (5 + multiples of 8)
  int val = value_val->to_int();
  assert((val & 1) == 1);  // bit 0 is 1
  assert((val & 2) == 0);  // bit 1 is 0  
  assert((val & 4) == 4);  // bit 2 is 1
  
  solver->pop(1);
  
  cout << "Bit manipulation test PASSED" << endl;
}

void test_power_of_two()
{
  cout << "=== Testing Power of Two Constraints ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term value = solver->make_symbol("value", bv8);
  
  // Value should be a power of 2: value & (value - 1) == 0 and value > 0
  Term one = solver->make_term(1, bv8);
  Term zero = solver->make_term(0, bv8);
  
  Term value_minus_one = solver->make_term(BVSub, value, one);
  Term and_result = solver->make_term(BVAnd, value, value_minus_one);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, and_result, zero));
  solver->assert_formula(solver->make_term(BVUgt, value, zero));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term value_val = solver->get_value(value);
  int val = value_val->to_int();
  
  cout << "Power of 2: " << val << endl;
  
  // Verify it's actually a power of 2
  assert(val > 0);
  assert((val & (val - 1)) == 0);
  
  solver->pop(1);
  
  cout << "Power of two test PASSED" << endl;
}

void test_byte_operations()
{
  cout << "=== Testing Byte Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv16 = solver->make_sort(BV, 16);
  Sort bv8 = solver->make_sort(BV, 8);
  
  Term word = solver->make_symbol("word", bv16);
  
  // Extract high and low bytes
  Op extract_high(Extract, 15, 8);
  Op extract_low(Extract, 7, 0);
  
  Term high_byte = solver->make_term(extract_high, word);
  Term low_byte = solver->make_term(extract_low, word);
  
  // Set constraints: high byte = 0xAB, low byte = 0xCD
  Term val_AB = solver->make_term(0xAB, bv8);
  Term val_CD = solver->make_term(0xCD, bv8);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, high_byte, val_AB));
  solver->assert_formula(solver->make_term(Equal, low_byte, val_CD));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term word_val = solver->get_value(word);
  cout << "Word value: 0x" << hex << word_val->to_int() << dec << endl;
  
  assert(word_val->to_int() == 0xABCD);
  
  solver->pop(1);
  
  cout << "Byte operations test PASSED" << endl;
}

void test_linear_congruence()
{
  cout << "=== Testing Linear Congruence ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Term x = solver->make_symbol("x", bv8);
  
  // Find x such that 3*x ≡ 5 (mod 7) in 8-bit arithmetic
  // This means (3*x - 5) % 7 == 0
  Term three = solver->make_term(3, bv8);
  Term five = solver->make_term(5, bv8);
  Term seven = solver->make_term(7, bv8);
  Term zero = solver->make_term(0, bv8);
  
  Term three_x = solver->make_term(BVMul, three, x);
  Term three_x_minus_five = solver->make_term(BVSub, three_x, five);
  Term remainder = solver->make_term(BVUrem, three_x_minus_five, seven);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, remainder, zero));
  solver->assert_formula(solver->make_term(BVUlt, x, solver->make_term(50, bv8))); // Keep x reasonable
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term x_val = solver->get_value(x);
  cout << "Solution to 3x ≡ 5 (mod 7): x = " << x_val->to_int() << endl;
  
  // Verify the solution
  int x_int = x_val->to_int();
  assert(((3 * x_int - 5) % 7) == 0);
  
  solver->pop(1);
  
  cout << "Linear congruence test PASSED" << endl;
}

void test_bit_counting()
{
  cout << "=== Testing Bit Counting ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort bv4 = solver->make_sort(BV, 4);
  
  Term value = solver->make_symbol("value", bv8);
  Term count = solver->make_symbol("count", bv4);
  
  // Count number of 1 bits in value (population count)
  // For simplicity, let's count bits manually for an 8-bit value
  vector<Term> bits;
  for (int i = 0; i < 8; i++) {
    Op extract_bit(Extract, i, i);
    Term bit = solver->make_term(extract_bit, value);
    
    // Convert 1-bit BV to 4-bit BV for addition
    Sort bv1 = solver->make_sort(BV, 1);
    Term zero_3bits = solver->make_term("000", solver->make_sort(BV, 3), 2);
    Term bit_extended = solver->make_term(Concat, zero_3bits, bit);
    bits.push_back(bit_extended);
  }
  
  // Sum all bits
  Term sum = bits[0];
  for (int i = 1; i < 8; i++) {
    sum = solver->make_term(BVAdd, sum, bits[i]);
  }
  
  // Value should have exactly 3 ones
  Term three = solver->make_term(3, bv4);
  
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, sum, three));
  solver->assert_formula(solver->make_term(Equal, count, sum));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term value_val = solver->get_value(value);
  Term count_val = solver->get_value(count);
  
  cout << "Value: " << value_val->to_int() << " (binary: ";
  int val = value_val->to_int();
  for (int i = 7; i >= 0; i--) {
    cout << ((val >> i) & 1);
  }
  cout << "), Bit count: " << count_val->to_int() << endl;
  
  // Verify bit count
  int actual_count = 0;
  for (int i = 0; i < 8; i++) {
    if (val & (1 << i)) actual_count++;
  }
  assert(actual_count == 3);
  assert(count_val->to_int() == 3);
  
  solver->pop(1);
  
  cout << "Bit counting test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Simple Bit-Vector Tests..." << endl;
    
    test_simple_arithmetic_constraints();
    test_range_constraints();
    test_bit_manipulation();
    test_power_of_two();
    test_byte_operations();
    test_linear_congruence();
    test_bit_counting();
    
    cout << "All STP Simple Bit-Vector Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 