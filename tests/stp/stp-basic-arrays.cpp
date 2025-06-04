/*********************                                                        */
/*! \file stp-basic-arrays.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Basic array tests for STP solver
**        Tests fundamental array operations, select/store, and basic constraints
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_array_sorts()
{
  cout << "=== Testing Array Sorts ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  // Test different array sorts
  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort bv16 = solver->make_sort(BV, 16);
  
  Sort arr4_8 = solver->make_sort(ARRAY, bv4, bv8);   // 4-bit index, 8-bit value
  Sort arr8_16 = solver->make_sort(ARRAY, bv8, bv16); // 8-bit index, 16-bit value
  Sort arr8_8 = solver->make_sort(ARRAY, bv8, bv8);   // 8-bit index, 8-bit value
  
  // Test that different array sorts are distinct
  assert(arr4_8 != arr8_16);
  assert(arr4_8 != arr8_8);
  assert(arr8_16 != arr8_8);
  
  // Test index and element sort retrieval
  assert(arr4_8->get_indexsort() == bv4);
  assert(arr4_8->get_elemsort() == bv8);
  assert(arr8_16->get_indexsort() == bv8);
  assert(arr8_16->get_elemsort() == bv16);
  
  cout << "Array sorts test PASSED" << endl;
}

void test_array_variables()
{
  cout << "=== Testing Array Variables ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  // Create array variables
  Term arr1 = solver->make_symbol("arr1", arr_sort);
  Term arr2 = solver->make_symbol("arr2", arr_sort);
  Term arr3 = solver->make_symbol("arr3", arr_sort);
  
  // Test that variables are distinct
  assert(arr1 != arr2);
  assert(arr2 != arr3);
  assert(arr1 != arr3);
  
  // Test that array variables have correct sorts
  assert(arr1->get_sort() == arr_sort);
  assert(arr2->get_sort() == arr_sort);
  assert(arr3->get_sort() == arr_sort);
  
  cout << "Array variables test PASSED" << endl;
}

void test_basic_select_operations()
{
  cout << "=== Testing Basic Select Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term idx_0 = solver->make_term(0, bv4);
  Term idx_5 = solver->make_term(5, bv4);
  Term val_42 = solver->make_term(42, bv8);
  Term val_100 = solver->make_term(100, bv8);
  
  // Test basic select operation
  Term select_0 = solver->make_term(Select, arr, idx_0);
  Term select_5 = solver->make_term(Select, arr, idx_5);
  
  // Test that select returns correct sort
  assert(select_0->get_sort() == bv8);
  assert(select_5->get_sort() == bv8);
  
  // Test constraint: arr[0] = 42
  solver->push(1);
  solver->assert_formula(solver->make_term(Equal, select_0, val_42));
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Check that we can get the value
  Term select_0_val = solver->get_value(select_0);
  assert(select_0_val->to_int() == 42);
  solver->pop(1);
  
  cout << "Basic select operations test PASSED" << endl;
}

void test_basic_store_operations()
{
  cout << "=== Testing Basic Store Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term idx_3 = solver->make_term(3, bv4);
  Term val_77 = solver->make_term(77, bv8);
  
  // Test store operation: arr' = store(arr, 3, 77)
  Term arr_updated = solver->make_term(Store, arr, idx_3, val_77);
  
  // Test that store returns correct sort
  assert(arr_updated->get_sort() == arr_sort);
  
  // Test that arr'[3] = 77
  solver->push(1);
  Term select_3 = solver->make_term(Select, arr_updated, idx_3);
  solver->assert_formula(solver->make_term(Equal, select_3, val_77));
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Verify the value
  Term select_3_val = solver->get_value(select_3);
  assert(select_3_val->to_int() == 77);
  solver->pop(1);
  
  cout << "Basic store operations test PASSED" << endl;
}

void test_select_store_axioms()
{
  cout << "=== Testing Select-Store Axioms ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term idx1 = solver->make_term(1, bv4);
  Term idx2 = solver->make_term(2, bv4);
  Term val_50 = solver->make_term(50, bv8);
  
  // Test axiom: select(store(arr, i, v), i) = v
  solver->push(1);
  Term arr_stored = solver->make_term(Store, arr, idx1, val_50);
  Term select_stored = solver->make_term(Select, arr_stored, idx1);
  solver->assert_formula(solver->make_term(Equal, select_stored, val_50));
  Result r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  // Test axiom: i != j => select(store(arr, i, v), j) = select(arr, j)
  solver->push(1);
  Term arr_stored2 = solver->make_term(Store, arr, idx1, val_50);
  Term select_different = solver->make_term(Select, arr_stored2, idx2);
  Term select_original = solver->make_term(Select, arr, idx2);
  solver->assert_formula(solver->make_term(Equal, select_different, select_original));
  r = solver->check_sat();
  assert(r.is_sat());
  solver->pop(1);
  
  cout << "Select-store axioms test PASSED" << endl;
}

void test_array_equality()
{
  cout << "=== Testing Array Equality (Element-wise) ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr1 = solver->make_symbol("arr1", arr_sort);
  Term arr2 = solver->make_symbol("arr2", arr_sort);
  Term idx = solver->make_term(7, bv4);
  Term val = solver->make_term(88, bv8);
  
  // Set both arrays to have the same value at a specific index
  Term arr1_updated = solver->make_term(Store, arr1, idx, val);
  Term arr2_updated = solver->make_term(Store, arr2, idx, val);
  
  // Test that arrays with same element values have equal elements at that index
  solver->push(1);
  Term select1 = solver->make_term(Select, arr1_updated, idx);
  Term select2 = solver->make_term(Select, arr2_updated, idx);
  solver->assert_formula(solver->make_term(Equal, select1, select2));
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Verify the values are indeed equal
  Term select1_val = solver->get_value(select1);
  Term select2_val = solver->get_value(select2);
  assert(select1_val->to_int() == select2_val->to_int());
  assert(select1_val->to_int() == 88);
  
  solver->pop(1);
  
  // Test that arrays can have different values at different indices
  solver->push(1);
  Term idx2 = solver->make_term(3, bv4);
  Term val1 = solver->make_term(100, bv8);
  Term val2 = solver->make_term(200, bv8);
  
  Term arr1_diff = solver->make_term(Store, arr1, idx2, val1);
  Term arr2_diff = solver->make_term(Store, arr2, idx2, val2);
  
  Term select1_diff = solver->make_term(Select, arr1_diff, idx2);
  Term select2_diff = solver->make_term(Select, arr2_diff, idx2);
  
  // Assert they have different values
  solver->assert_formula(solver->make_term(Equal, select1_diff, val1));
  solver->assert_formula(solver->make_term(Equal, select2_diff, val2));
  solver->assert_formula(solver->make_term(Not, solver->make_term(Equal, select1_diff, select2_diff)));
  
  r = solver->check_sat();
  assert(r.is_sat());
  
  solver->pop(1);
  
  cout << "Array equality (element-wise) test PASSED" << endl;
}

void test_multiple_stores()
{
  cout << "=== Testing Multiple Store Operations ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term idx1 = solver->make_term(1, bv4);
  Term idx2 = solver->make_term(2, bv4);
  Term idx3 = solver->make_term(3, bv4);
  Term val10 = solver->make_term(10, bv8);
  Term val20 = solver->make_term(20, bv8);
  Term val30 = solver->make_term(30, bv8);
  
  // Chain multiple stores: arr[1] = 10, arr[2] = 20, arr[3] = 30
  Term arr1 = solver->make_term(Store, arr, idx1, val10);
  Term arr2 = solver->make_term(Store, arr1, idx2, val20);
  Term arr3 = solver->make_term(Store, arr2, idx3, val30);
  
  // Test that all values are correctly stored
  solver->push(1);
  Term select1 = solver->make_term(Select, arr3, idx1);
  Term select2 = solver->make_term(Select, arr3, idx2);
  Term select3 = solver->make_term(Select, arr3, idx3);
  
  solver->assert_formula(solver->make_term(Equal, select1, val10));
  solver->assert_formula(solver->make_term(Equal, select2, val20));
  solver->assert_formula(solver->make_term(Equal, select3, val30));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Verify values
  Term select1_val = solver->get_value(select1);
  Term select2_val = solver->get_value(select2);
  Term select3_val = solver->get_value(select3);
  
  assert(select1_val->to_int() == 10);
  assert(select2_val->to_int() == 20);
  assert(select3_val->to_int() == 30);
  
  solver->pop(1);
  
  cout << "Multiple stores test PASSED" << endl;
}

void test_array_models()
{
  cout << "=== Testing Array Models ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term idx1 = solver->make_term(5, bv4);
  Term idx2 = solver->make_term(10, bv4);
  Term val1 = solver->make_term(111, bv8);
  Term val2 = solver->make_term(222, bv8);
  
  // Constrain array at specific indices
  solver->push(1);
  Term select1 = solver->make_term(Select, arr, idx1);
  Term select2 = solver->make_term(Select, arr, idx2);
  
  solver->assert_formula(solver->make_term(Equal, select1, val1));
  solver->assert_formula(solver->make_term(Equal, select2, val2));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  // Get array model
  Term const_base;
  UnorderedTermMap array_assignments = solver->get_array_values(arr, const_base);
  
  // Should have at least the two assignments we specified
  assert(array_assignments.size() >= 2);
  
  bool found_idx1 = false, found_idx2 = false;
  for (const auto& assignment : array_assignments) {
    if (assignment.first->to_int() == 5) {
      assert(assignment.second->to_int() == 111);
      found_idx1 = true;
    }
    if (assignment.first->to_int() == 10) {
      assert(assignment.second->to_int() == 222);
      found_idx2 = true;
    }
  }
  
  assert(found_idx1 && found_idx2);
  
  solver->pop(1);
  
  cout << "Array models test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Basic Array Tests..." << endl;
    
    test_array_sorts();
    test_array_variables();
    test_basic_select_operations();
    test_basic_store_operations();
    test_select_store_axioms();
    test_array_equality();
    test_multiple_stores();
    test_array_models();
    
    cout << "All STP Basic Array Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 