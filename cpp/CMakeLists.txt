cmake_minimum_required(VERSION 3.15)

project(smt_wire_cpp LANGUAGES CXX)

add_library(smt_wire INTERFACE)
add_library(smt_wire::smt_wire ALIAS smt_wire)

target_compile_features(smt_wire INTERFACE cxx_std_17)
target_include_directories(
  smt_wire
  INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

if(WIN32)
  target_link_libraries(smt_wire INTERFACE ws2_32)
endif()

if(CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR)
  set(SMT_WIRE_CPP_BUILD_TESTS_DEFAULT ON)
else()
  set(SMT_WIRE_CPP_BUILD_TESTS_DEFAULT OFF)
endif()
option(SMT_WIRE_CPP_BUILD_TESTS "Build smt-wire C++ tests" ${SMT_WIRE_CPP_BUILD_TESTS_DEFAULT})

if(SMT_WIRE_CPP_BUILD_TESTS)
  enable_testing()

  add_executable(smt_wire_cpp_smoke tests/cpp_client_smoke.cpp)
  target_link_libraries(smt_wire_cpp_smoke PRIVATE smt_wire::smt_wire)
  target_compile_options(smt_wire_cpp_smoke PRIVATE
    $<$<CXX_COMPILER_ID:MSVC>:/W4 /WX>
    $<$<NOT:$<CXX_COMPILER_ID:MSVC>>:-Wall -Wextra -Werror>
  )
  add_test(NAME smt_wire_cpp_smoke COMMAND smt_wire_cpp_smoke)

  add_executable(smt_wire_cpp_live_client tests/cpp_live_client.cpp)
  target_link_libraries(smt_wire_cpp_live_client PRIVATE smt_wire::smt_wire)
  target_compile_options(smt_wire_cpp_live_client PRIVATE
    $<$<CXX_COMPILER_ID:MSVC>:/W4 /WX>
    $<$<NOT:$<CXX_COMPILER_ID:MSVC>>:-Wall -Wextra -Werror>
  )

  add_executable(smt_wire_cpp_example example.cpp)
  target_link_libraries(smt_wire_cpp_example PRIVATE smt_wire::smt_wire)
  target_compile_options(smt_wire_cpp_example PRIVATE
    $<$<CXX_COMPILER_ID:MSVC>:/W4 /WX>
    $<$<NOT:$<CXX_COMPILER_ID:MSVC>>:-Wall -Wextra -Werror>
  )
endif()
