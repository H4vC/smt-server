cmake_minimum_required(VERSION 3.15)

project(smt_server LANGUAGES CXX)

option(SMT_WIRE_CPP_BUILD_TESTS "Build smt-wire C++ tests" ON)

enable_testing()
add_subdirectory(cpp)
