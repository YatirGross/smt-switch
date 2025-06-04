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

switch_add_stp_test(stp-simple)
switch_add_stp_test(stp-simple-unsat)
switch_add_stp_test(stp-arrays)
switch_add_stp_test(stp-incremental)
switch_add_stp_test(stp-bitvector)