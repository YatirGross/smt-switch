/*********************                                                        */
/*! \file stp-array-simple.cpp
** \verbatim
** Top contributors (to current version):
**   [Your name here]
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Simple array tests for STP solver
**        Tests basic array manipulation and access patterns
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "stp_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

void test_simple_array_initialization()
{
  cout << "=== Testing Simple Array Initialization ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  
  // Initialize array with specific values at key indices
  Term arr1 = solver->make_term(Store, arr, solver->make_term(0, bv4), solver->make_term(10, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(1, bv4), solver->make_term(20, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(2, bv4), solver->make_term(30, bv8));
  
  solver->push(1);
  
  // Access the stored values
  Term val0 = solver->make_term(Select, arr3, solver->make_term(0, bv4));
  Term val1 = solver->make_term(Select, arr3, solver->make_term(1, bv4));
  Term val2 = solver->make_term(Select, arr3, solver->make_term(2, bv4));
  
  solver->assert_formula(solver->make_term(Equal, val0, solver->make_term(10, bv8)));
  solver->assert_formula(solver->make_term(Equal, val1, solver->make_term(20, bv8)));
  solver->assert_formula(solver->make_term(Equal, val2, solver->make_term(30, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Array initialized: arr[0]=10, arr[1]=20, arr[2]=30" << endl;
  
  solver->pop(1);
  
  cout << "Simple array initialization test PASSED" << endl;
}

void test_array_lookup_table()
{
  cout << "=== Testing Array as Lookup Table ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term lookup_table = solver->make_symbol("lookup_table", arr_sort);
  Term input = solver->make_symbol("input", bv4);
  Term output = solver->make_symbol("output", bv8);
  
  // Create a simple lookup table: square function for values 0-3
  Term table1 = solver->make_term(Store, lookup_table, solver->make_term(0, bv4), solver->make_term(0, bv8));   // 0^2 = 0
  Term table2 = solver->make_term(Store, table1, solver->make_term(1, bv4), solver->make_term(1, bv8));         // 1^2 = 1
  Term table3 = solver->make_term(Store, table2, solver->make_term(2, bv4), solver->make_term(4, bv8));         // 2^2 = 4
  Term table_final = solver->make_term(Store, table3, solver->make_term(3, bv4), solver->make_term(9, bv8));    // 3^2 = 9
  
  solver->push(1);
  
  // Lookup operation
  Term lookup_result = solver->make_term(Select, table_final, input);
  solver->assert_formula(solver->make_term(Equal, output, lookup_result));
  
  // Test lookup for input = 2
  solver->assert_formula(solver->make_term(Equal, input, solver->make_term(2, bv4)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term output_val = solver->get_value(output);
  cout << "Lookup table[2] = " << output_val->to_int() << endl;
  assert(output_val->to_int() == 4);
  
  solver->pop(1);
  
  cout << "Array lookup table test PASSED" << endl;
}

void test_array_swap_elements()
{
  cout << "=== Testing Array Element Swap ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr_before = solver->make_symbol("arr_before", arr_sort);
  Term arr_after = solver->make_symbol("arr_after", arr_sort);
  
  Term idx1 = solver->make_term(3, bv4);
  Term idx2 = solver->make_term(7, bv4);
  Term val1 = solver->make_term(100, bv8);
  Term val2 = solver->make_term(200, bv8);
  
  // Setup initial array state: arr_before[3] = 100, arr_before[7] = 200
  Term initial1 = solver->make_term(Store, arr_before, idx1, val1);
  Term initial2 = solver->make_term(Store, initial1, idx2, val2);
  
  // Create swapped array: arr_after[3] = 200, arr_after[7] = 100 (values swapped)
  Term swapped1 = solver->make_term(Store, arr_after, idx1, val2);  // arr_after[3] = 200
  Term swapped2 = solver->make_term(Store, swapped1, idx2, val1);   // arr_after[7] = 100
  
  solver->push(1);
  
  // Assert the initial state
  solver->assert_formula(solver->make_term(Equal, solver->make_term(Select, initial2, idx1), val1));
  solver->assert_formula(solver->make_term(Equal, solver->make_term(Select, initial2, idx2), val2));
  
  // Assert the swapped state
  solver->assert_formula(solver->make_term(Equal, solver->make_term(Select, swapped2, idx1), val2));
  solver->assert_formula(solver->make_term(Equal, solver->make_term(Select, swapped2, idx2), val1));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Array elements swapped: arr[3] and arr[7]" << endl;
  
  solver->pop(1);
  
  cout << "Array element swap test PASSED" << endl;
}

void test_array_range_assignment()
{
  cout << "=== Testing Array Range Assignment ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term pattern_value = solver->make_term(42, bv8);
  
  // Set a range of indices to the same value
  Term arr1 = solver->make_term(Store, arr, solver->make_term(5, bv4), pattern_value);
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(6, bv4), pattern_value);
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(7, bv4), pattern_value);
  Term arr4 = solver->make_term(Store, arr3, solver->make_term(8, bv4), pattern_value);
  
  solver->push(1);
  
  // Verify all values in range are set correctly
  for (int i = 5; i <= 8; i++) {
    Term val = solver->make_term(Select, arr4, solver->make_term(i, bv4));
    solver->assert_formula(solver->make_term(Equal, val, pattern_value));
  }
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Array range [5,8] set to value 42" << endl;
  
  solver->pop(1);
  
  cout << "Array range assignment test PASSED" << endl;
}

void test_array_copy_operation()
{
  cout << "=== Testing Array Copy Operation ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term source_arr = solver->make_symbol("source_arr", arr_sort);
  Term dest_arr = solver->make_symbol("dest_arr", arr_sort);
  
  // Initialize source array
  Term src1 = solver->make_term(Store, source_arr, solver->make_term(0, bv4), solver->make_term(11, bv8));
  Term src2 = solver->make_term(Store, src1, solver->make_term(1, bv4), solver->make_term(22, bv8));
  Term src3 = solver->make_term(Store, src2, solver->make_term(2, bv4), solver->make_term(33, bv8));
  
  // Copy operation: copy from source indices 0,1,2 to dest indices 1,2,3
  Term src_val0 = solver->make_term(Select, src3, solver->make_term(0, bv4));
  Term src_val1 = solver->make_term(Select, src3, solver->make_term(1, bv4));
  Term src_val2 = solver->make_term(Select, src3, solver->make_term(2, bv4));
  
  Term dest1 = solver->make_term(Store, dest_arr, solver->make_term(1, bv4), src_val0);
  Term dest2 = solver->make_term(Store, dest1, solver->make_term(2, bv4), src_val1);
  Term dest3 = solver->make_term(Store, dest2, solver->make_term(3, bv4), src_val2);
  
  solver->push(1);
  
  // Verify copy
  Term dest_val1 = solver->make_term(Select, dest3, solver->make_term(1, bv4));
  Term dest_val2 = solver->make_term(Select, dest3, solver->make_term(2, bv4));
  Term dest_val3 = solver->make_term(Select, dest3, solver->make_term(3, bv4));
  
  solver->assert_formula(solver->make_term(Equal, dest_val1, solver->make_term(11, bv8)));
  solver->assert_formula(solver->make_term(Equal, dest_val2, solver->make_term(22, bv8)));
  solver->assert_formula(solver->make_term(Equal, dest_val3, solver->make_term(33, bv8)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  cout << "Array copy: source[0,1,2] -> dest[1,2,3]" << endl;
  
  solver->pop(1);
  
  cout << "Array copy operation test PASSED" << endl;
}

void test_array_search_operation()
{
  cout << "=== Testing Array Search Operation ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  Sort bool_sort = solver->make_sort(BOOL);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term search_value = solver->make_term(77, bv8);
  Term found_index = solver->make_symbol("found_index", bv4);
  Term found = solver->make_symbol("found", bool_sort);
  
  // Setup array with known values
  Term arr1 = solver->make_term(Store, arr, solver->make_term(1, bv4), solver->make_term(10, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(3, bv4), solver->make_term(77, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(5, bv4), solver->make_term(25, bv8));
  Term arr4 = solver->make_term(Store, arr3, solver->make_term(7, bv4), solver->make_term(77, bv8));
  
  solver->push(1);
  
  // Search constraint: found iff arr[found_index] == search_value
  Term found_value = solver->make_term(Select, arr4, found_index);
  Term value_matches = solver->make_term(Equal, found_value, search_value);
  solver->assert_formula(solver->make_term(Equal, found, value_matches));
  
  // Assert that we found the value
  solver->assert_formula(found);
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term index_val = solver->get_value(found_index);
  Term found_val = solver->get_value(found);
  
  cout << "Found value 77 at index: " << index_val->to_int() << endl;
  assert(found_val->to_int() == 1); // true
  assert(index_val->to_int() == 3 || index_val->to_int() == 7); // Either valid index
  
  solver->pop(1);
  
  cout << "Array search operation test PASSED" << endl;
}

void test_array_maximum_element()
{
  cout << "=== Testing Array Maximum Element ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_ABV");
  solver->set_opt("produce-models", "true");

  Sort bv4 = solver->make_sort(BV, 4);
  Sort bv8 = solver->make_sort(BV, 8);
  Sort arr_sort = solver->make_sort(ARRAY, bv4, bv8);
  
  Term arr = solver->make_symbol("arr", arr_sort);
  Term max_value = solver->make_symbol("max_value", bv8);
  Term max_index = solver->make_symbol("max_index", bv4);
  
  // Setup array with known values (indices 0-3)
  Term arr1 = solver->make_term(Store, arr, solver->make_term(0, bv4), solver->make_term(15, bv8));
  Term arr2 = solver->make_term(Store, arr1, solver->make_term(1, bv4), solver->make_term(30, bv8));
  Term arr3 = solver->make_term(Store, arr2, solver->make_term(2, bv4), solver->make_term(25, bv8));
  Term arr4 = solver->make_term(Store, arr3, solver->make_term(3, bv4), solver->make_term(10, bv8));
  
  solver->push(1);
  
  // max_value should be the value at max_index
  Term value_at_max = solver->make_term(Select, arr4, max_index);
  solver->assert_formula(solver->make_term(Equal, max_value, value_at_max));
  
  // max_value should be >= all other values in array
  for (int i = 0; i < 4; i++) {
    Term idx = solver->make_term(i, bv4);
    Term val_at_i = solver->make_term(Select, arr4, idx);
    solver->assert_formula(solver->make_term(BVUge, max_value, val_at_i));
  }
  
  // max_index should be in valid range
  solver->assert_formula(solver->make_term(BVUle, max_index, solver->make_term(3, bv4)));
  
  Result r = solver->check_sat();
  assert(r.is_sat());
  
  Term max_val = solver->get_value(max_value);
  Term max_idx = solver->get_value(max_index);
  
  cout << "Maximum value: " << max_val->to_int() << " at index " << max_idx->to_int() << endl;
  assert(max_val->to_int() == 30);  // Should find the maximum value
  assert(max_idx->to_int() == 1);   // Should be at index 1
  
  solver->pop(1);
  
  cout << "Array maximum element test PASSED" << endl;
}

int main()
{
  try {
    cout << "Starting STP Simple Array Tests..." << endl;
    
    test_simple_array_initialization();
    test_array_lookup_table();
    test_array_swap_elements();
    test_array_range_assignment();
    test_array_copy_operation();
    test_array_search_operation();
    test_array_maximum_element();
    
    cout << "All STP Simple Array Tests PASSED!" << endl;
    return 0;
  }
  catch (const exception& e) {
    cout << "Test FAILED with exception: " << e.what() << endl;
    return 1;
  }
} 