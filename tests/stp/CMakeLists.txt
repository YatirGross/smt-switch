# Set the build type to Debug to include debug symbols
set(CMAKE_BUILD_TYPE Debug)

# Ensure the -g flag is added to the compiler options
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -g")

macro(switch_add_stp_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/stp/${name}.cpp")
  target_link_libraries(${name} gtest gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

# Basic functionality tests
switch_add_stp_test(stp-basic-bool)
switch_add_stp_test(stp-basic-bv)
switch_add_stp_test(stp-basic-arrays)

# Simple operations tests
switch_add_stp_test(stp-bool-simple)
switch_add_stp_test(stp-bv-simple)
switch_add_stp_test(stp-array-simple)

# Complex operations tests  
switch_add_stp_test(stp-bool-complex)
switch_add_stp_test(stp-bv-complex)
switch_add_stp_test(stp-array-complex)

# Integration tests
switch_add_stp_test(stp-integration)

# Edge cases and regression tests
switch_add_stp_test(stp-edge-cases)

# Performance and stress tests
switch_add_stp_test(stp-performance)

# Legacy tests (keep for compatibility)
switch_add_stp_test(stp-simple)
switch_add_stp_test(stp-simple-unsat)
switch_add_stp_test(stp-arrays)
switch_add_stp_test(stp-incremental)
switch_add_stp_test(stp-bitvector)