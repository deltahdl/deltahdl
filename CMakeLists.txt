cmake_minimum_required(VERSION 3.28)
project(deltahdl VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# With the standard at 20 or above, CMake has Ninja scan every source for C++
# module imports and exports before compiling any of it, and no source here
# declares or imports one. The scan is a preprocessor pass per source that
# finds nothing, one step per object ahead of the objects -- 520 of the 1,040
# steps of build-coverage-lib, 12 of its 201 seconds in run 35657769589 --
# and the objects wait on the whole of it.
set(CMAKE_CXX_SCAN_FOR_MODULES OFF)

option(DELTAHDL_COVERAGE "Enable code coverage instrumentation" OFF)
option(DELTAHDL_SANITIZERS "Enable ASan + UBSan" OFF)
option(DELTAHDL_TSAN "Enable ThreadSanitizer" OFF)

# Instrumented objects are large and there are thousands of executables to link
# them into, which makes linking the dominant cost of a coverage build. lld is
# the linker that comes with the toolchain doing the compiling, and it does that
# work several times faster than the default. Confined to this configuration:
# nothing else here links enough to notice, and the released binary is built by
# whatever linker its platform supplies.
if(DELTAHDL_COVERAGE)
    add_compile_options(-fprofile-instr-generate -fcoverage-mapping)
    add_link_options(-fprofile-instr-generate -fcoverage-mapping -fuse-ld=lld)
endif()

if(DELTAHDL_SANITIZERS)
    add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer)
    add_link_options(-fsanitize=address,undefined)
endif()

if(DELTAHDL_TSAN)
    add_compile_options(-fsanitize=thread -fno-omit-frame-pointer)
    add_link_options(-fsanitize=thread)
endif()

add_compile_options(-Wall -Wextra -Wpedantic -Werror)

# src/simulator/vpi_user.h is Annex K.2's file as the standard prints it and is
# not edited. Its portability help takes the sized types from <inttypes.h> on
# Linux and from <sys/types.h> on any platform it does not name, and Apple's
# SDK declares int64_t and u_int64_t there but no uint64_t, so the annex's
# `typedef uint64_t PLI_UINT64;` fails on macOS in every translation unit that
# reads the file before <cstdint>. Each translation unit therefore begins with
# <stdint.h> on macOS, which is what <inttypes.h> gives the annex on Linux.
if(APPLE)
    add_compile_options(-include stdint.h)
endif()

add_subdirectory(src)

include(CTest)
if(BUILD_TESTING)
    add_subdirectory(test)
    add_test(
        NAME sim_tests
        COMMAND ${CMAKE_COMMAND} -E env
            PYTHONPATH=${CMAKE_CURRENT_SOURCE_DIR}:${CMAKE_CURRENT_SOURCE_DIR}/scripts
            python3 -m run_sim_tests
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )
    set_tests_properties(sim_tests PROPERTIES LABELS "e2e")
endif()
