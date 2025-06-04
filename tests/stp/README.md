# STP Solver Tests

This directory contains comprehensive tests for the STP solver integration with smt-switch. The tests are organized by complexity and theory coverage, providing thorough validation of STP's capabilities in bit-vectors (BV), boolean logic (BOOL), and arrays (ARRAYS).

## Test Organization

### Basic Tests (Fundamental Operations)
- **`stp-basic-bool.cpp`** - Boolean constants, variables, basic operations (AND, OR, NOT, XOR), truth tables, implications, and ITE
- **`stp-basic-bv.cpp`** - Bit-vector sorts, constants, variables, arithmetic operations, bitwise operations, comparisons, shifts, extract/concat
- **`stp-basic-arrays.cpp`** - Array sorts, variables, select/store operations, axioms, equality, and models

### Simple Tests (Real-world Scenarios)
- **`stp-bool-simple.cpp`** - Common boolean patterns and simple satisfiability problems
- **`stp-bv-simple.cpp`** - Practical bit-vector constraints and common use cases
- **`stp-array-simple.cpp`** - Basic array manipulation and access patterns

### Complex Tests (Advanced Operations)
- **`stp-bool-complex.cpp`** - Complex boolean formulas, nested operations, and edge cases
- **`stp-bv-complex.cpp`** - Advanced bit-vector operations including:
  - Overflow/underflow behavior
  - Signed vs unsigned operations
  - Division and modulo operations
  - Advanced bitwise operations (NAND, NOR, XNOR)
  - Complex extract/concat patterns
  - Edge cases and boundary conditions
- **`stp-array-complex.cpp`** - Complex array operations and advanced constraints

### Integration Tests
- **`stp-integration.cpp`** - Tests combining multiple theories:
  - Boolean-controlled bit-vector operations
  - Arrays with bit-vector indices and conditions
  - Boolean arrays (using 1-bit BVs)
  - Conditional array updates
  - Array bounds checking
  - Complex search algorithms
  - Mixed theory constraints

### Specialized Tests
- **`stp-edge-cases.cpp`** - Edge cases, corner cases, and regression tests
- **`stp-performance.cpp`** - Performance and stress tests

### Legacy Tests (For Compatibility)
- **`stp-simple.cpp`** - Original simple test
- **`stp-simple-unsat.cpp`** - Original unsat test
- **`stp-arrays.cpp`** - Original array test
- **`stp-incremental.cpp`** - Incremental solving test
- **`stp-bitvector.cpp`** - Original bitvector test

## STP Capabilities Tested

### Supported Theories
- **QF_BV** (Quantifier-Free Bit-Vectors)
- **QF_ABV** (Quantifier-Free Arrays of Bit-Vectors)
- **BOOL** (Boolean logic)

### Supported Operations

#### Boolean Operations
- Constants: `true`, `false`
- Logical: `AND`, `OR`, `NOT`, `XOR`, `IMPLIES`, `ITE`
- Equality and comparison

#### Bit-Vector Operations
- **Arithmetic**: `BVAdd`, `BVSub`, `BVMul`, `BVUdiv`, `BVSdiv`, `BVUrem`, `BVSrem`, `BVSmod`
- **Bitwise**: `BVAnd`, `BVOr`, `BVXor`, `BVNot`, `BVNand`, `BVNor`, `BVXnor`
- **Shifts**: `BVShl`, `BVLshr`, `BVAshr`
- **Comparison**: `BVUlt`, `BVUle`, `BVUgt`, `BVUge`, `BVSlt`, `BVSle`, `BVSgt`, `BVSge`
- **Manipulation**: `Extract`, `Concat`
- **Equality**: `Equal`, `Distinct`

#### Array Operations
- **Access**: `Select` (array read)
- **Update**: `Store` (array write)
- **Equality**: Array equality and inequality
- **Models**: Array model extraction

### Bit-Vector Widths Tested
- 1-bit (boolean-like)
- 4-bit (nibbles)
- 8-bit (bytes)
- 16-bit (words)
- 32-bit (double words)

## Running the Tests

### Individual Tests
```bash
# Build and run a specific test
make stp-basic-bool
./stp-basic-bool

# Build and run all STP tests
make all
ctest -R stp
```

### Test Categories
```bash
# Basic tests
ctest -R "stp-basic"

# Complex tests  
ctest -R "stp.*complex"

# Integration tests
ctest -R "stp-integration"

# All new organized tests (excluding legacy)
ctest -R "stp-(basic|simple|complex|integration|edge|performance)"
```

### Expected Output
Each test provides verbose output showing:
- Test section headers (e.g., "=== Testing Boolean Constants ===")
- Progress indicators for each test case
- Final success message: "All STP [Category] Tests PASSED!"
- Error details if any test fails

## Test Design Principles

### Readability
- Clear, descriptive test names and section headers
- Comprehensive comments explaining complex operations
- Logical organization from simple to complex

### Coverage
- **Functional Coverage**: All supported operations and edge cases
- **Boundary Testing**: Min/max values, overflow/underflow conditions
- **Error Conditions**: Invalid operations and edge cases
- **Integration Testing**: Cross-theory interactions

### Maintainability
- Modular test functions with single responsibilities
- Consistent coding style and patterns
- Reusable helper functions where appropriate
- Clear separation between test categories

### Verification
- Assertions on satisfiability results
- Model value verification
- Cross-validation of equivalent operations
- Negative testing (UNSAT cases)

## Common Patterns

### Test Structure
```cpp
void test_feature_name()
{
  cout << "=== Testing Feature Name ===" << endl;
  
  SmtSolver solver = StpSolverFactory::create(false);
  solver->set_logic("QF_BV" /* or "QF_ABV" */);
  solver->set_opt("produce-models", "true");

  // Test setup
  Sort sort = solver->make_sort(BV, 8);
  Term var = solver->make_symbol("var", sort);
  
  // Test execution
  solver->push(1);
  solver->assert_formula(/* constraints */);
  Result r = solver->check_sat();
  assert(r.is_sat() /* or r.is_unsat() */);
  
  // Verification
  if (r.is_sat()) {
    Term val = solver->get_value(var);
    assert(val->to_int() == expected_value);
  }
  
  solver->pop(1);
  
  cout << "Feature name test PASSED" << endl;
}
```

### Error Handling
All tests include proper exception handling and provide descriptive error messages when failures occur.

## Contributing

When adding new tests:

1. **Choose the appropriate category** (basic, simple, complex, integration)
2. **Follow naming conventions**: `stp-[category]-[theory].cpp`
3. **Include comprehensive documentation** in comments
4. **Test both SAT and UNSAT cases** where applicable
5. **Verify model values** when testing SAT cases
6. **Add the test to CMakeLists.txt**

## Known Limitations

STP in smt-switch supports:
- ✅ Bit-vectors (QF_BV)
- ✅ Arrays of bit-vectors (QF_ABV) 
- ✅ Boolean logic
- ❌ Quantifiers
- ❌ Uninterpreted functions
- ❌ Integer/Real arithmetic
- ❌ Strings
- ❌ Datatypes

Tests are designed to work within these supported capabilities. 