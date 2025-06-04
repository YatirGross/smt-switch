set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Configure RPATH for automatic library discovery
set(CMAKE_SKIP_BUILD_RPATH FALSE)
set(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)
set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)

find_library(LIBRT rt)

add_library(smt-switch-stp "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/stp_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/stp_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/stp_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/stp_term.cpp"
  )

target_include_directories (smt-switch-stp PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-stp PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-stp PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/stp/include")
target_include_directories (smt-switch-stp PUBLIC "${STP_HOME}/lib")
target_include_directories (smt-switch-stp PUBLIC "${STP_HOME}/include")
target_include_directories (smt-switch-stp PUBLIC "${STP_HOME}/build/include")
target_include_directories (smt-switch-stp PUBLIC ${GMP_INCLUDE_DIR})

if (LIBRT)
  target_link_libraries(smt-switch-stp ${LIBRT})
endif()

target_link_libraries(smt-switch-stp stp)
target_link_libraries(smt-switch-stp smt-switch)
target_link_libraries(smt-switch-stp pthread)
target_link_libraries(smt-switch-stp m)

find_library(MINISAT_LIB REQUIRED
             NAMES libminisat.so.2.1.0 libminisat.so.2 libminisat.so
             PATHS "${STP_HOME}/deps/install/lib")

find_library(CRYPTOMINISAT_LIB REQUIRED
             NAMES libcryptominisat5.so.5.11
             PATHS "${STP_HOME}/deps/install/lib")

find_library(CADIBACK_LIB REQUIRED
             NAMES libcadiback.so
             PATHS "${STP_HOME}/deps/install/lib")

find_library(CADICAL REQUIRED
             NAMES libcadical.so
             PATHS "${STP_HOME}/deps/install/lib"
             )

target_link_libraries(smt-switch-stp "${MINISAT_LIB}")
target_link_libraries(smt-switch-stp "${CRYPTOMINISAT_LIB}")
target_link_libraries(smt-switch-stp "${CADIBACK_LIB}")
target_link_libraries(smt-switch-stp "${CADICAL}")
target_link_libraries(smt-switch-stp ${GMP_LIBRARIES})

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the stp source and dependencies (except GMP)
  # use libtool to combine
  add_custom_command(
    OUTPUT static-smt-switch-stp.stamp
    COMMAND
      mkdir ssc-working && cd ssc-working &&
      # create new static library that combines them all
      ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh "$<TARGET_FILE_NAME:smt-switch-stp>" "${MINISAT_LIB}" "${CRYPTOMINISAT_LIB}" "${CADIBACK_LIB}" "${CADICAL}" "../$<TARGET_FILE_NAME:smt-switch-stp>" &&
      # replace the original one
      mv "$<TARGET_FILE_NAME:smt-switch-stp>" "../$<TARGET_FILE_NAME:smt-switch-stp>" &&
      # now clean up the temporary directory
      cd ../ && rm -rf ssc-working
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-stp.stamp
    DEPENDS
      smt-switch-stp
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
    )

  add_custom_target(
    repack-stp-static-lib ALL
    DEPENDS static-smt-switch-stp.stamp
    )
endif()

install(TARGETS smt-switch-stp DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
