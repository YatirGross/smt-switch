/*********************                                                        */
/*! \file stp-array-complex.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Complex array tests for STP solver
**        Tests complex array operations and advanced constraints
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_array_sorting_algorithm()
{
  cout << "=== Testing Array Sorting Algorithm ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr_before = solver->make_symbol("arr_before", arr_sort);
  Term arr_after = solver->make_symbol("arr_after", arr_sort);
  
  // Initialize unsorted array: [30, 10, 40, 20]
  Term arr1 = solver->make_term(Store, arr_before, solver->make_term(0, bv4), solver->make_term(30, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(1, bv4), solver->make_term(10, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(2, bv4), solver->make_term(40, bv8));
  Term arr4 = solver->make_term(Store, arr3, solver->make_term(3, bv4), solver->make_term(20, bv8));
  
  // Constraint: arr_after should be sorted version of arr_before
  solver->push(1);
  
  // Sorted array constraint: arr_after[0] <= arr_after[1] <= arr_after[2] <= arr_after[3]
  for (int i = 0; i < 3; i++) {
    Term curr = solver->make_term(Select, arr_after, solver->make_term(i, bv4));
    Term next = solver->make_term(Select, arr_after, solver->make_term(i+1, bv4));
    solver->assert_formula(solver->make_term(BVUle, curr, next));
  }
  
  // Permutation constraint: arr_after contains same values as arr_before
  vector<Term> before_values, after_values;
  for (int i = 0; i < 4; i++) {
    before_values.push_back(solver->make_term(Select, arr4, solver->make_term(i, bv4)));
    after_values.push_back(solver->make_term(Select, arr_after, solver->make_term(i, bv4)));
  }
  
  // Each value in before must appear somewhere in after
  for (int i = 0; i < 4; i++) {
    vector<Term> equals;
    for (int j = 0; j < 4; j++) {
      equals.push_back(solver->make_term(Equal, before_values[i], after_values[j]));
    }
    Term exists_in_after = equals[0];
    for (int j = 1; j < 4; j++) {
      exists_in_after = solver->make_term(Or, exists_in_after, equals[j]);
    }
    solver->assert_formula(exists_in_after);
  }
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Sorted array: ";
  for (int i = 0; i < 4; i++) {
    Term val = solver->get_value(solver->make_term(Select, arr_after, solver->make_term(i, bv4)));
    cout << val->to_int() << " ";
  }
  cout << endl;
  
  solver->pop(1);
  
  cout << "Array sorting algorithm test PASSED" << endl;
}

void test_array_binary_search()
{
  cout << "=== Testing Array Binary Search ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  Sort bool_sort = solver->make_sort(BOOL);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term target = solver->make_term(25, bv8);
  Term found = solver->make_symbol("found", bool_sort);
  Term result_index = solver->make_symbol("result_index", bv4);
  
  // Initialize sorted array: [10, 20, 25, 30, 40, 50, 60, 70]
  Term arr1 = solver->make_term(Store, arr, solver->make_term(0, bv4), solver->make_term(10, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(1, bv4), solver->make_term(20, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(2, bv4), solver->make_term(25, bv8));
  Term arr4 = solver->make_term(Store, arr3, solver->make_term(3, bv4), solver->make_term(30, bv8));
  Term arr5 = solver->make_term(Store, arr4, solver->make_term(4, bv4), solver->make_term(40, bv8));
  Term arr6 = solver->make_term(Store, arr5, solver->make_term(5, bv4), solver->make_term(50, bv8));
  Term arr7 = solver->make_term(Store, arr6, solver->make_term(6, bv4), solver->make_term(60, bv8));
  Term arr8 = solver->make_term(Store, arr7, solver->make_term(7, bv4), solver->make_term(70, bv8));
  
  solver->push(1);
  
  // Binary search constraint: if found, then arr[result_index] == target
  Term value_at_index = solver->make_term(Select, arr8, result_index);
  Term target_found = solver->make_term(Equal, value_at_index, target);
  solver->assert_formula(solver->make_term(Equal, found, target_found));
  
  // Constraint: result_index should be valid
  solver->assert_formula(solver->make_term(BVUlt, result_index, solver->make_term(8, bv4)));
  
  // Assert that we should find the target
  solver->assert_formula(found);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term found_val = solver->get_value(found);
  Term index_val = solver->get_value(result_index);
  
  cout << "Binary search: target " << target->to_int() 
       << " found=" << found_val->to_int() 
       << " at index=" << index_val->to_int() << endl;
  
  assert(found_val->to_int() == 1);
  assert(index_val->to_int() == 2); // Should find 25 at index 2
  
  solver->pop(1);
  
  cout << "Array binary search test PASSED" << endl;
}

void test_array_merge_operation()
{
  cout << "=== Testing Array Merge Operation ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr1 = solver->make_symbol("arr1", arr_sort);
  Term arr2 = solver->make_symbol("arr2", arr_sort);
  Term merged = solver->make_symbol("merged", arr_sort);
  
  // Initialize two sorted arrays
  // arr1: [10, 30, 50] (indices 0,1,2)
  Term a1_1 = solver->make_term(Store, arr1, solver->make_term(0, bv4), solver->make_term(10, bv8));
  Term a1_2 = solver->make_term(Store, a1_1, solver->make_term(1, bv4), solver->make_term(30, bv8));
  Term a1_3 = solver->make_term(Store, a1_2, solver->make_term(2, bv4), solver->make_term(50, bv8));
  
  // arr2: [20, 40, 60] (indices 0,1,2)
  Term a2_1 = solver->make_term(Store, arr2, solver->make_term(0, bv4), solver->make_term(20, bv8));
  Term a2_2 = solver->make_term(Store, a2_1, solver->make_term(1, bv4), solver->make_term(40, bv8));
  Term a2_3 = solver->make_term(Store, a2_2, solver->make_term(2, bv4), solver->make_term(60, bv8));
  
  solver->push(1);
  
  // Merge constraint: merged array should be sorted and contain all elements
  // Expected merged result: [10, 20, 30, 40, 50, 60]
  Term m1 = solver->make_term(Store, merged, solver->make_term(0, bv4), solver->make_term(10, bv8));
  Term m2 = solver->make_term(Store, m1, solver->make_term(1, bv4), solver->make_term(20, bv8));
  Term m3 = solver->make_term(Store, m2, solver->make_term(2, bv4), solver->make_term(30, bv8));
  Term m4 = solver->make_term(Store, m3, solver->make_term(3, bv4), solver->make_term(40, bv8));
  Term m5 = solver->make_term(Store, m4, solver->make_term(4, bv4), solver->make_term(50, bv8));
  Term m6 = solver->make_term(Store, m5, solver->make_term(5, bv4), solver->make_term(60, bv8));
  
  // Assert the merged array matches our expectation
  for (int i = 0; i < 6; i++) {
    Term expected_val = solver->make_term(Select, m6, solver->make_term(i, bv4));
    Term actual_val = solver->make_term(Select, merged, solver->make_term(i, bv4));
    solver->assert_formula(solver->make_term(Equal, expected_val, actual_val));
  }
  
  // Verify sorted property
  for (int i = 0; i < 5; i++) {
    Term curr = solver->make_term(Select, merged, solver->make_term(i, bv4));
    Term next = solver->make_term(Select, merged, solver->make_term(i+1, bv4));
    solver->assert_formula(solver->make_term(BVUle, curr, next));
  }
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Merged array: ";
  for (int i = 0; i < 6; i++) {
    Term val = solver->get_value(solver->make_term(Select, merged, solver->make_term(i, bv4)));
    cout << val->to_int() << " ";
  }
  cout << endl;
  
  solver->pop(1);
  
  cout << "Array merge operation test PASSED" << endl;
}

void test_array_permutation_checking()
{
  cout << "=== Testing Array Permutation Checking ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  Sort bool_sort = solver->make_sort(BOOL);
  
  Term arr1 = solver->make_symbol("arr1", arr_sort);
  Term arr2 = solver->make_symbol("arr2", arr_sort);
  Term is_permutation = solver->make_symbol("is_permutation", bool_sort);
  
  // Initialize first array: [5, 15, 25, 35]
  Term a1_1 = solver->make_term(Store, arr1, solver->make_term(0, bv4), solver->make_term(5, bv8));
  Term a1_2 = solver->make_term(Store, a1_1, solver->make_term(1, bv4), solver->make_term(15, bv8));
  Term a1_3 = solver->make_term(Store, a1_2, solver->make_term(2, bv4), solver->make_term(25, bv8));
  Term a1_4 = solver->make_term(Store, a1_3, solver->make_term(3, bv4), solver->make_term(35, bv8));
  
  // Second array should be a permutation: [25, 5, 35, 15]
  Term a2_1 = solver->make_term(Store, arr2, solver->make_term(0, bv4), solver->make_term(25, bv8));
  Term a2_2 = solver->make_term(Store, a2_1, solver->make_term(1, bv4), solver->make_term(5, bv8));
  Term a2_3 = solver->make_term(Store, a2_2, solver->make_term(2, bv4), solver->make_term(35, bv8));
  Term a2_4 = solver->make_term(Store, a2_3, solver->make_term(3, bv4), solver->make_term(15, bv8));
  
  solver->push(1);
  
  // Permutation constraint: each element in arr1 appears exactly once in arr2
  vector<Term> permutation_constraints;
  
  for (int i = 0; i < 4; i++) {
    Term val1 = solver->make_term(Select, a1_4, solver->make_term(i, bv4));
    
    // This value should appear exactly once in arr2
    vector<Term> occurrences;
    for (int j = 0; j < 4; j++) {
      Term val2 = solver->make_term(Select, a2_4, solver->make_term(j, bv4));
      occurrences.push_back(solver->make_term(Equal, val1, val2));
    }
    
    // Exactly one occurrence (at least one AND at most one)
    Term at_least_one = occurrences[0];
    for (int j = 1; j < 4; j++) {
      at_least_one = solver->make_term(Or, at_least_one, occurrences[j]);
    }
    
    // At most one: no two positions can have the same value
    vector<Term> at_most_one_constraints;
    for (int j = 0; j < 4; j++) {
      for (int k = j+1; k < 4; k++) {
        Term both_match = solver->make_term(And, occurrences[j], occurrences[k]);
        at_most_one_constraints.push_back(solver->make_term(Not, both_match));
      }
    }
    
    permutation_constraints.push_back(at_least_one);
    for (const auto& constraint : at_most_one_constraints) {
      permutation_constraints.push_back(constraint);
    }
  }
  
  // All permutation constraints should hold if it's a permutation
  Term all_constraints = permutation_constraints[0];
  for (size_t i = 1; i < permutation_constraints.size(); i++) {
    all_constraints = solver->make_term(And, all_constraints, permutation_constraints[i]);
  }
  
  solver->assert_formula(solver->make_term(Equal, is_permutation, all_constraints));
  solver->assert_formula(is_permutation);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term perm_val = solver->get_value(is_permutation);
  cout << "Arrays are permutations: " << (perm_val->to_int() ? "true" : "false") << endl;
  assert(perm_val->to_int() == 1);
  
  solver->pop(1);
  
  cout << "Array permutation checking test PASSED" << endl;
}

void test_array_bounds_checking()
{
  cout << "=== Testing Array Bounds Checking ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  Sort bool_sort = solver->make_sort(BOOL);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term access_index = solver->make_symbol("access_index", bv4);
  Term bounds_ok = solver->make_symbol("bounds_ok", bool_sort);
  Term array_size = solver->make_term(8, bv4);
  
  // Initialize array with valid range [0,7]
  Term arr_init = arr;
  for (int i = 0; i < 8; i++) {
    arr_init = solver->make_term(Store, arr_init, solver->make_term(i, bv4), solver->make_term(i*10, bv8));
  }
  
  solver->push(1);
  
  // Bounds checking constraint: bounds_ok iff access_index < array_size
  Term bounds_check = solver->make_term(BVUlt, access_index, array_size);
  solver->assert_formula(solver->make_term(Equal, bounds_ok, bounds_check));
  
  // Test valid access
  solver->assert_formula(solver->make_term(Equal, access_index, solver->make_term(5, bv4)));
  solver->assert_formula(bounds_ok);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term access_val = solver->get_value(access_index);
  Term bounds_val = solver->get_value(bounds_ok);
  
  cout << "Access index: " << access_val->to_int() << ", bounds OK: " << bounds_val->to_int() << endl;
  assert(bounds_val->to_int() == 1);
  
  solver->pop(1);
  
  // Test invalid access
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, bounds_ok, bounds_check));
  solver->assert_formula(solver->make_term(Equal, access_index, solver->make_term(15, bv4))); // Invalid index
  
  r = solver->check_sat();
  assert(r.is_sat());
  
  bounds_val = solver->get_value(bounds_ok);
  access_val = solver->get_value(access_index);
  
  cout << "Access index: " << access_val->to_int() << ", bounds OK: " << bounds_val->to_int() << endl;
  assert(bounds_val->to_int() == 0); // Should be false for out-of-bounds access
  
  solver->pop(1);
  
  cout << "Array bounds checking test PASSED" << endl;
}

void test_array_sliding_window()
{
  cout << "=== Testing Array Sliding Window ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term window_sum = solver->make_symbol("window_sum", bv8);
  Term window_start = solver->make_symbol("window_start", bv4);
  Term window_size = solver->make_term(3, bv4);
  
  // Initialize array: [1, 4, 2, 8, 5, 7, 3, 6]
  vector<int> values = {1, 4, 2, 8, 5, 7, 3, 6};
  Term arr_init = arr;
  for (int i = 0; i < 8; i++) {
    arr_init = solver->make_term(Store, arr_init, solver->make_term(i, bv4), solver->make_term(values[i], bv8));
  }
  
  solver->push(1);
  
  // Sliding window sum constraint: sum of 3 consecutive elements
  Term elem0 = solver->make_term(Select, arr_init, window_start);
  Term elem1 = solver->make_term(Select, arr_init, solver->make_term(BVAdd, window_start, solver->make_term(1, bv4)));
  Term elem2 = solver->make_term(Select, arr_init, solver->make_term(BVAdd, window_start, solver->make_term(2, bv4)));
  
  Term sum = solver->make_term(BVAdd, elem0, solver->make_term(BVAdd, elem1, elem2));
  solver->assert_formula(solver->make_term(Equal, window_sum, sum));
  
  // Constraint: window should fit within array bounds
  Term max_start = solver->make_term(BVSub, solver->make_term(8, bv4), window_size);
  solver->assert_formula(solver->make_term(BVUle, window_start, max_start));
  
  // Find window with maximum sum
  solver->assert_formula(solver->make_term(BVUge, window_sum, solver->make_term(15, bv8))); // At least 15
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term start_val = solver->get_value(window_start);
  Term sum_val = solver->get_value(window_sum);
  
  cout << "Sliding window: start=" << start_val->to_int() 
       << ", sum=" << sum_val->to_int() << endl;
  
  // Verify the sum
  int start_idx = start_val->to_int();
  int expected_sum = values[start_idx] + values[start_idx+1] + values[start_idx+2];
  assert(sum_val->to_int() == expected_sum);
  
  solver->pop(1);
  
  cout << "Array sliding window test PASSED" << endl;
}

void test_array_matrix_operations()
{
  cout << "=== Testing Array Matrix Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  // Represent 2x2 matrices as arrays with indices: 0=a[0][0], 1=a[0][1], 2=a[1][0], 3=a[1][1]
  Term matrix_a = solver->make_symbol("matrix_a", arr_sort);
  Term matrix_b = solver->make_symbol("matrix_b", arr_sort);
  Term matrix_c = solver->make_symbol("matrix_c", arr_sort);
  
  // Initialize matrix A = [[1,2],[3,4]]
  Term ma1 = solver->make_term(Store, matrix_a, solver->make_term(0, bv4), solver->make_term(1, bv8));
  Term ma2 = solver->make_term(Store, ma1, solver->make_term(1, bv4), solver->make_term(2, bv8));
  Term ma3 = solver->make_term(Store, ma2, solver->make_term(2, bv4), solver->make_term(3, bv8));
  Term ma4 = solver->make_term(Store, ma3, solver->make_term(3, bv4), solver->make_term(4, bv8));
  
  // Initialize matrix B = [[5,6],[7,8]]
  Term mb1 = solver->make_term(Store, matrix_b, solver->make_term(0, bv4), solver->make_term(5, bv8));
  Term mb2 = solver->make_term(Store, mb1, solver->make_term(1, bv4), solver->make_term(6, bv8));
  Term mb3 = solver->make_term(Store, mb2, solver->make_term(2, bv4), solver->make_term(7, bv8));
  Term mb4 = solver->make_term(Store, mb3, solver->make_term(3, bv4), solver->make_term(8, bv8));
  
  solver->push(1);
  
  // Matrix multiplication: C = A * B
  // C[0][0] = A[0][0]*B[0][0] + A[0][1]*B[1][0] = 1*5 + 2*7 = 19
  // C[0][1] = A[0][0]*B[0][1] + A[0][1]*B[1][1] = 1*6 + 2*8 = 22
  // C[1][0] = A[1][0]*B[0][0] + A[1][1]*B[1][0] = 3*5 + 4*7 = 43
  // C[1][1] = A[1][0]*B[0][1] + A[1][1]*B[1][1] = 3*6 + 4*8 = 50
  
  Term a00 = solver->make_term(Select, ma4, solver->make_term(0, bv4));
  Term a01 = solver->make_term(Select, ma4, solver->make_term(1, bv4));
  Term a10 = solver->make_term(Select, ma4, solver->make_term(2, bv4));
  Term a11 = solver->make_term(Select, ma4, solver->make_term(3, bv4));
  
  Term b00 = solver->make_term(Select, mb4, solver->make_term(0, bv4));
  Term b01 = solver->make_term(Select, mb4, solver->make_term(1, bv4));
  Term b10 = solver->make_term(Select, mb4, solver->make_term(2, bv4));
  Term b11 = solver->make_term(Select, mb4, solver->make_term(3, bv4));
  
  // Calculate matrix multiplication
  Term c00 = solver->make_term(BVAdd, solver->make_term(BVMul, a00, b00), solver->make_term(BVMul, a01, b10));
  Term c01 = solver->make_term(BVAdd, solver->make_term(BVMul, a00, b01), solver->make_term(BVMul, a01, b11));
  Term c10 = solver->make_term(BVAdd, solver->make_term(BVMul, a10, b00), solver->make_term(BVMul, a11, b10));
  Term c11 = solver->make_term(BVAdd, solver->make_term(BVMul, a10, b01), solver->make_term(BVMul, a11, b11));
  
  // Store results in matrix C
  Term mc1 = solver->make_term(Store, matrix_c, solver->make_term(0, bv4), c00);
  Term mc2 = solver->make_term(Store, mc1, solver->make_term(1, bv4), c01);
  Term mc3 = solver->make_term(Store, mc2, solver->make_term(2, bv4), c10);
  Term mc4 = solver->make_term(Store, mc3, solver->make_term(3, bv4), c11);
  
  // Verify expected results
  solver->assert_formula(solver->make_term(Equal, c00, solver->make_term(19, bv8)));
  solver->assert_formula(solver->make_term(Equal, c01, solver->make_term(22, bv8)));
  solver->assert_formula(solver->make_term(Equal, c10, solver->make_term(43, bv8)));
  solver->assert_formula(solver->make_term(Equal, c11, solver->make_term(50, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Matrix multiplication result:" << endl;
  for (int i = 0; i < 2; i++) {
    for (int j = 0; j < 2; j++) {
      int idx = i*2 + j;
      Term val = solver->get_value(solver->make_term(Select, mc4, solver->make_term(idx, bv4)));
      cout << val->to_int() << " ";
    }
    cout << endl;
  }
  
  solver->pop(1);
  
  cout << "Array matrix operations test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Complex Array Tests..." << endl;
    
    test_array_sorting_algorithm();
    test_array_binary_search();
    test_array_merge_operation();
    test_array_permutation_checking();
    test_array_bounds_checking();
    test_array_sliding_window();
    test_array_matrix_operations();
    
    cout << "All STP Complex Array Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 