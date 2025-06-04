/*********************                                                        */
/*! \file stp-integration.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Integration tests for STP solver
**        Tests complex interactions between BV, BOOL, and ARRAYS
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_conditional_array_access()
{
  cout << "=== Testing Conditional Array Access (BV + BOOL + ARRAYS) ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv8, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term index = solver->make_symbol("index", bv8);
  Term condition = solver->make_symbol("condition", bool_sort);
  Term result = solver->make_symbol("result", bv8);
  
  // Initialize array with some values
  Term arr1 = solver->make_term(Store, arr, solver->make_term(5, bv8), solver->make_term(50, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(10, bv8), solver->make_term(100, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(15, bv8), solver->make_term(150, bv8));
  
  solver->push(1);
  
  // Conditional access: if condition then arr[index], else default value
  Term array_access = solver->make_term(Select, arr3, index);
  Term default_value = solver->make_term(255, bv8);
  Term conditional_result = solver->make_term(Ite, condition, array_access, default_value);
  
  solver->assert_formula(solver->make_term(Equal, result, conditional_result));
  
  // Test case: condition = true, index = 10
  solver->assert_formula(condition);
  solver->assert_formula(solver->make_term(Equal, index, solver->make_term(10, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term result_val = solver->get_value(result);
  Term condition_val = solver->get_value(condition);
  Term index_val = solver->get_value(index);
  
  cout << "Condition: " << condition_val->to_int() 
       << ", Index: " << index_val->to_int() 
       << ", Result: " << result_val->to_int() << endl;
  
  assert(result_val->to_int() == 100); // Should get arr[10] = 100
  
  solver->pop(1);
  
  cout << "Conditional array access test PASSED" << endl;
}

void test_array_based_lookup_with_bitvector_arithmetic()
{
  cout << "=== Testing Array-Based Lookup with Bit-Vector Arithmetic ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term lookup_table = solver->make_symbol("lookup_table", arr_sort);
  Term input_a = solver->make_symbol("input_a", bv4);
  Term input_b = solver->make_symbol("input_b", bv4);
  Term output = solver->make_symbol("output", bv8);
  
  // Create multiplication table: table[i] = i * 7
  Term table_init = lookup_table;
  for (int i = 0; i < 16; i++) {
    table_init = solver->make_term(Store, table_init, 
                                   solver->make_term(i, bv4), 
                                   solver->make_term((i * 7) % 256, bv8));
  }
  
  solver->push(1);
  
  // Compute index = (input_a + input_b) % 16
  Term sum = solver->make_term(BVAdd, input_a, input_b);
  Term masked_sum = solver->make_term(BVAnd, sum, solver->make_term(15, bv4)); // % 16
  
  // Lookup result in table
  Term lookup_result = solver->make_term(Select, table_init, masked_sum);
  solver->assert_formula(solver->make_term(Equal, output, lookup_result));
  
  // Test with specific inputs
  solver->assert_formula(solver->make_term(Equal, input_a, solver->make_term(3, bv4)));
  solver->assert_formula(solver->make_term(Equal, input_b, solver->make_term(5, bv4)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term a_val = solver->get_value(input_a);
  Term b_val = solver->get_value(input_b);
  Term output_val = solver->get_value(output);
  
  cout << "Input A: " << a_val->to_int() 
       << ", Input B: " << b_val->to_int() 
       << ", Output: " << output_val->to_int() << endl;
  
  // Verify: (3 + 5) % 16 = 8, table[8] = 8 * 7 = 56
  assert(output_val->to_int() == 56);
  
  solver->pop(1);
  
  cout << "Array-based lookup with bit-vector arithmetic test PASSED" << endl;
}

void test_boolean_controlled_array_operations()
{
  cout << "=== Testing Boolean-Controlled Array Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr_original = solver->make_symbol("arr_original", arr_sort);
  Term arr_result = solver->make_symbol("arr_result", arr_sort);
  Term enable_write = solver->make_symbol("enable_write", bool_sort);
  Term write_index = solver->make_symbol("write_index", bv4);
  Term write_value = solver->make_symbol("write_value", bv8);
  Term result_value = solver->make_symbol("result_value", bv8);
  
  // Initialize original array with some values
  Term arr1 = solver->make_term(Store, arr_original, solver->make_term(0, bv4), solver->make_term(10, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(1, bv4), solver->make_term(20, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(2, bv4), solver->make_term(30, bv8));
  
  solver->push(1);
  
  // Test the boolean-controlled write operation
  // If enable_write is true, result should have write_value at write_index
  // Otherwise, result should have original value at write_index
  
  Term original_value_at_index = solver->make_term(Select, arr3, write_index);
  Term conditional_value = solver->make_term(Ite, enable_write, write_value, original_value_at_index);
  
  // Set up the result array with the conditional value
  Term arr_with_conditional = solver->make_term(Store, arr_result, write_index, conditional_value);
  
  // Get the actual result value
  Term actual_result = solver->make_term(Select, arr_with_conditional, write_index);
  solver->assert_formula(solver->make_term(Equal, result_value, actual_result));
  
  // Test scenario: enable write, write 99 to index 1
  solver->assert_formula(enable_write);
  solver->assert_formula(solver->make_term(Equal, write_index, solver->make_term(1, bv4)));
  solver->assert_formula(solver->make_term(Equal, write_value, solver->make_term(99, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Verify the write happened
  Term result_val = solver->get_value(result_value);
  Term enable_val = solver->get_value(enable_write);
  Term write_val = solver->get_value(write_value);
  
  cout << "Write enabled: " << enable_val->to_int() 
       << ", Expected value: " << write_val->to_int()
       << ", Actual result: " << result_val->to_int() << endl;
  
  assert(result_val->to_int() == 99);
  
  solver->pop(1);
  
  cout << "Boolean-controlled array operations test PASSED" << endl;
}

void test_bitvector_array_indexing_with_bounds_check()
{
  cout << "=== Testing Bit-Vector Array Indexing with Bounds Check ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term raw_index = solver->make_symbol("raw_index", bv8);
  Term safe_index = solver->make_symbol("safe_index", bv4);
  Term bounds_ok = solver->make_symbol("bounds_ok", bool_sort);
  Term result = solver->make_symbol("result", bv8);
  
  // Initialize array with 8 elements (indices 0-7)
  Term arr_init = arr;
  for (int i = 0; i < 8; i++) {
    arr_init = solver->make_term(Store, arr_init, solver->make_term(i, bv4), solver->make_term(i * 10 + 5, bv8));
  }
  
  solver->push(1);
  
  // Bounds checking: bounds_ok if raw_index < 8
  Term bounds_check = solver->make_term(BVUlt, raw_index, solver->make_term(8, bv8));
  solver->assert_formula(solver->make_term(Equal, bounds_ok, bounds_check));
  
  // Safe indexing: if bounds OK, use raw_index (truncated), else use 0
  Op extract_low4(Extract, 3, 0);
  Term truncated_index = solver->make_term(extract_low4, raw_index);
  Term safe_idx = solver->make_term(Ite, bounds_ok, truncated_index, solver->make_term(0, bv4));
  solver->assert_formula(solver->make_term(Equal, safe_index, safe_idx));
  
  // Array access with safe index
  Term array_result = solver->make_term(Select, arr_init, safe_index);
  solver->assert_formula(solver->make_term(Equal, result, array_result));
  
  // Test with valid index
  solver->assert_formula(solver->make_term(Equal, raw_index, solver->make_term(5, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term raw_val = solver->get_value(raw_index);
  Term safe_val = solver->get_value(safe_index);
  Term bounds_val = solver->get_value(bounds_ok);
  Term result_val = solver->get_value(result);
  
  cout << "Raw index: " << raw_val->to_int() 
       << ", Safe index: " << safe_val->to_int() 
       << ", Bounds OK: " << bounds_val->to_int() 
       << ", Result: " << result_val->to_int() << endl;
  
  assert(bounds_val->to_int() == 1);
  assert(safe_val->to_int() == 5);
  assert(result_val->to_int() == 55); // arr[5] = 5*10 + 5 = 55
  
  solver->pop(1);
  
  cout << "Bit-vector array indexing with bounds check test PASSED" << endl;
}

void test_complex_data_structure_simulation()
{
  cout << "=== Testing Complex Data Structure Simulation ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  // Simulate a simple hash table with linear probing
  Term hash_table = solver->make_symbol("hash_table", arr_sort);
  Term occupied = solver->make_symbol("occupied", arr_sort); // Boolean array (0/1)
  Term key = solver->make_symbol("key", bv8);
  Term value = solver->make_symbol("value", bv8);
  Term insert_success = solver->make_symbol("insert_success", bool_sort);
  Term final_slot = solver->make_symbol("final_slot", bv4);
  
  // Initialize empty hash table (all slots unoccupied)
  Term occ_init = occupied;
  Term hash_init = hash_table;
  for (int i = 0; i < 8; i++) {
    occ_init = solver->make_term(Store, occ_init, solver->make_term(i, bv4), solver->make_term(0, bv8));
    hash_init = solver->make_term(Store, hash_init, solver->make_term(i, bv4), solver->make_term(0, bv8));
  }
  
  solver->push(1);
  
  // Hash function: hash = key % 8
  Op extract_low3(Extract, 2, 0);
  Term hash_value = solver->make_term(extract_low3, key);
  Term hash_4bit = solver->make_term(Concat, solver->make_term(0, solver->make_sort(BV, 1)), hash_value);
  
  // Linear probing: find first empty slot starting from hash_value
  vector<Term> slot_constraints;
  
  for (int i = 0; i < 8; i++) {
    // Calculate probe slot: (hash_value + i) % 8
    Term probe_offset = solver->make_term(i, bv4);
    Term probe_slot = solver->make_term(BVAnd, 
                                        solver->make_term(BVAdd, hash_4bit, probe_offset),
                                        solver->make_term(7, bv4)); // % 8
    
    // Check if this slot is empty
    Term slot_occupied = solver->make_term(Select, occ_init, probe_slot);
    Term slot_empty = solver->make_term(Equal, slot_occupied, solver->make_term(0, bv8));
    
    // If this is the chosen slot
    Term is_final_slot = solver->make_term(Equal, final_slot, probe_slot);
    Term all_previous_occupied = solver->make_term(true);
    
    // All previous slots in probe sequence must be occupied
    for (int j = 0; j < i; j++) {
      Term prev_offset = solver->make_term(j, bv4);
      Term prev_slot = solver->make_term(BVAnd, 
                                         solver->make_term(BVAdd, hash_4bit, prev_offset),
                                         solver->make_term(7, bv4));
      Term prev_occupied = solver->make_term(Select, occ_init, prev_slot);
      Term prev_not_empty = solver->make_term(Equal, prev_occupied, solver->make_term(1, bv8));
      all_previous_occupied = solver->make_term(And, all_previous_occupied, prev_not_empty);
    }
    
    // Constraint: if this is final slot, then it's empty and all previous are occupied
    Term slot_constraint = solver->make_term(Implies, is_final_slot, 
                                           solver->make_term(And, slot_empty, all_previous_occupied));
    slot_constraints.push_back(slot_constraint);
  }
  
  // Apply all slot constraints
  for (const auto& constraint : slot_constraints) {
    solver->assert_formula(constraint);
  }
  
  // Insert should succeed (find an empty slot)
  solver->assert_formula(insert_success);
  Term final_slot_empty = solver->make_term(Select, occ_init, final_slot);
  solver->assert_formula(solver->make_term(Equal, insert_success, 
                                          solver->make_term(Equal, final_slot_empty, solver->make_term(0, bv8))));
  
  // Test insertion
  solver->assert_formula(solver->make_term(Equal, key, solver->make_term(42, bv8)));
  solver->assert_formula(solver->make_term(Equal, value, solver->make_term(100, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term key_val = solver->get_value(key);
  Term final_slot_val = solver->get_value(final_slot);
  Term success_val = solver->get_value(insert_success);
  
  cout << "Hash table insert: key=" << key_val->to_int() 
       << ", final_slot=" << final_slot_val->to_int() 
       << ", success=" << success_val->to_int() << endl;
  
  // Verify hash: 42 % 8 = 2, so should start probing from slot 2
  assert(success_val->to_int() == 1);
  
  solver->pop(1);
  
  cout << "Complex data structure simulation test PASSED" << endl;
}

void test_multi_dimensional_array_simulation()
{
  cout << "=== Testing Multi-Dimensional Array Simulation ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  // Simulate 4x4 matrix using 1D array with index = row*4 + col
  Term matrix = solver->make_symbol("matrix", arr_sort);
  Term row = solver->make_symbol("row", bv4);
  Term col = solver->make_symbol("col", bv4);
  Term value_at_pos = solver->make_symbol("value_at_pos", bv8);
  Term is_diagonal = solver->make_symbol("is_diagonal", bool_sort);
  
  // Initialize identity matrix
  Term matrix_init = matrix;
  for (int r = 0; r < 4; r++) {
    for (int c = 0; c < 4; c++) {
      int index = r * 4 + c;
      int val = (r == c) ? 1 : 0; // 1 on diagonal, 0 elsewhere
      matrix_init = solver->make_term(Store, matrix_init, 
                                      solver->make_term(index, bv4), 
                                      solver->make_term(val, bv8));
    }
  }
  
  solver->push(1);
  
  // Calculate linear index from 2D coordinates
  Term row_offset = solver->make_term(BVMul, row, solver->make_term(4, bv4));
  Term linear_index = solver->make_term(BVAdd, row_offset, col);
  
  // Access matrix element
  Term matrix_value = solver->make_term(Select, matrix_init, linear_index);
  solver->assert_formula(solver->make_term(Equal, value_at_pos, matrix_value));
  
  // Check if position is on diagonal
  Term on_diagonal = solver->make_term(Equal, row, col);
  solver->assert_formula(solver->make_term(Equal, is_diagonal, on_diagonal));
  
  // Test accessing diagonal element
  solver->assert_formula(solver->make_term(Equal, row, solver->make_term(2, bv4)));
  solver->assert_formula(solver->make_term(Equal, col, solver->make_term(2, bv4)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term row_val = solver->get_value(row);
  Term col_val = solver->get_value(col);
  Term value_val = solver->get_value(value_at_pos);
  Term diag_val = solver->get_value(is_diagonal);
  
  cout << "Matrix access: [" << row_val->to_int() << "][" << col_val->to_int() 
       << "] = " << value_val->to_int() 
       << ", is_diagonal = " << diag_val->to_int() << endl;
  
  assert(value_val->to_int() == 1); // Diagonal element should be 1
  assert(diag_val->to_int() == 1);  // Should be on diagonal
  
  solver->pop(1);
  
  cout << "Multi-dimensional array simulation test PASSED" << endl;
}

void test_state_machine_with_memory()
{
  cout << "=== Testing State Machine with Memory ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bool_sort = solver->make_sort(BOOL);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  // State machine with memory
  Term memory = solver->make_symbol("memory", arr_sort);
  Term current_state = solver->make_symbol("current_state", bv4);
  Term next_state = solver->make_symbol("next_state", bv4);
  Term input_signal = solver->make_symbol("input_signal", bv8);
  Term memory_updated = solver->make_symbol("memory_updated", bool_sort);
  Term output_value = solver->make_symbol("output_value", bv8);
  
  // Initialize memory with some values
  Term mem1 = solver->make_term(Store, memory, solver->make_term(0, bv4), solver->make_term(10, bv8));
  Term mem2 = solver->make_term(Store, mem1, solver->make_term(1, bv4), solver->make_term(20, bv8));
  Term mem3 = solver->make_term(Store, mem2, solver->make_term(2, bv4), solver->make_term(30, bv8));
  
  solver->push(1);
  
  // State transition logic
  // State 0: if input > 50, go to state 1, else stay in state 0
  // State 1: if input < 25, go to state 2, else go to state 0  
  // State 2: always go to state 0
  
  Term in_state0 = solver->make_term(Equal, current_state, solver->make_term(0, bv4));
  Term in_state1 = solver->make_term(Equal, current_state, solver->make_term(1, bv4));
  Term in_state2 = solver->make_term(Equal, current_state, solver->make_term(2, bv4));
  
  Term input_high = solver->make_term(BVUgt, input_signal, solver->make_term(50, bv8));
  Term input_low = solver->make_term(BVUlt, input_signal, solver->make_term(25, bv8));
  
  // State 0 transitions
  Term from0_to1 = solver->make_term(And, in_state0, input_high);
  Term from0_to0 = solver->make_term(And, in_state0, solver->make_term(Not, input_high));
  
  // State 1 transitions  
  Term from1_to2 = solver->make_term(And, in_state1, input_low);
  Term from1_to0 = solver->make_term(And, in_state1, solver->make_term(Not, input_low));
  
  // State 2 transitions
  Term from2_to0 = in_state2;
  
  // Next state logic
  Term next_is_0 = solver->make_term(Or, from0_to0, solver->make_term(Or, from1_to0, from2_to0));
  Term next_is_1 = from0_to1;
  Term next_is_2 = from1_to2;
  
  solver->assert_formula(solver->make_term(Implies, next_is_0, 
                                          solver->make_term(Equal, next_state, solver->make_term(0, bv4))));
  solver->assert_formula(solver->make_term(Implies, next_is_1, 
                                          solver->make_term(Equal, next_state, solver->make_term(1, bv4))));
  solver->assert_formula(solver->make_term(Implies, next_is_2, 
                                          solver->make_term(Equal, next_state, solver->make_term(2, bv4))));
  
  // Memory update: update memory[current_state] = input_signal when transitioning
  Term state_changed = solver->make_term(Not, solver->make_term(Equal, current_state, next_state));
  solver->assert_formula(solver->make_term(Equal, memory_updated, state_changed));
  
  // Output: read from memory[next_state]
  Term output = solver->make_term(Select, mem3, next_state);
  solver->assert_formula(solver->make_term(Equal, output_value, output));
  
  // Test scenario: current_state = 0, input = 75 (should transition to state 1)
  solver->assert_formula(solver->make_term(Equal, current_state, solver->make_term(0, bv4)));
  solver->assert_formula(solver->make_term(Equal, input_signal, solver->make_term(75, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term curr_val = solver->get_value(current_state);
  Term next_val = solver->get_value(next_state);
  Term input_val = solver->get_value(input_signal);
  Term updated_val = solver->get_value(memory_updated);
  Term output_val = solver->get_value(output_value);
  
  cout << "State machine: current=" << curr_val->to_int() 
       << ", input=" << input_val->to_int() 
       << ", next=" << next_val->to_int() 
       << ", memory_updated=" << updated_val->to_int() 
       << ", output=" << output_val->to_int() << endl;
  
  assert(next_val->to_int() == 1); // Should transition to state 1
  assert(updated_val->to_int() == 1); // Memory should be updated
  assert(output_val->to_int() == 20); // Output from memory[1] = 20
  
  solver->pop(1);
  
  cout << "State machine with memory test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Integration Tests..." << endl;
    
    test_conditional_array_access();
    test_array_based_lookup_with_bitvector_arithmetic();
    test_boolean_controlled_array_operations();
    test_bitvector_array_indexing_with_bounds_check();
    test_complex_data_structure_simulation();
    test_multi_dimensional_array_simulation();
    test_state_machine_with_memory();
    
    cout << "All STP Integration Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 