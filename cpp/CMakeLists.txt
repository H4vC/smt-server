cmake_minimum_required(VERSION 3.21)

project(smt_wire VERSION 0.1.0 LANGUAGES CXX)

include(CMakePackageConfigHelpers)
include(GNUInstallDirs)

option(SMT_WIRE_CPP_BUILD_TESTS "Build smt-wire C++ tests" ${PROJECT_IS_TOP_LEVEL})

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

install(
  TARGETS smt_wire
  EXPORT smt_wireTargets
  INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
install(
  DIRECTORY include/
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
install(
  EXPORT smt_wireTargets
  NAMESPACE smt_wire::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/smt_wire
)
configure_package_config_file(
  cmake/smt_wireConfig.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/smt_wireConfig.cmake
  INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/smt_wire
)
write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/smt_wireConfigVersion.cmake
  VERSION ${PROJECT_VERSION}
  COMPATIBILITY SameMajorVersion
)
install(
  FILES
    ${CMAKE_CURRENT_BINARY_DIR}/smt_wireConfig.cmake
    ${CMAKE_CURRENT_BINARY_DIR}/smt_wireConfigVersion.cmake
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/smt_wire
)

if(SMT_WIRE_CPP_BUILD_TESTS)
  enable_testing()
  set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

  add_executable(smoke tests/smoke.cpp)
  target_link_libraries(smoke PRIVATE smt_wire::smt_wire)
  add_test(NAME smoke COMMAND $<TARGET_FILE:smoke>)

  add_executable(example tests/example.cpp)
  target_link_libraries(example PRIVATE smt_wire::smt_wire)
  add_test(NAME example COMMAND $<TARGET_FILE:example>)
endif()
