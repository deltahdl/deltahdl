cmake_minimum_required(VERSION 3.28)
project(deltahdl VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(DELTAHDL_COVERAGE "Enable code coverage instrumentation" OFF)
option(DELTAHDL_SANITIZERS "Enable ASan + UBSan" OFF)

if(DELTAHDL_COVERAGE)
    add_compile_options(-fprofile-instr-generate -fcoverage-mapping)
    add_link_options(-fprofile-instr-generate -fcoverage-mapping)
endif()

if(DELTAHDL_SANITIZERS)
    add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer)
    add_link_options(-fsanitize=address,undefined)
endif()

add_compile_options(-Wall -Wextra -Wpedantic -Werror)

add_subdirectory(src)

include(CTest)
if(BUILD_TESTING)
    add_subdirectory(test)
    add_test(
        NAME sim_tests
        COMMAND ${CMAKE_COMMAND} -E env python3
            ${CMAKE_CURRENT_SOURCE_DIR}/scripts/run_sim_tests.py
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )
endif()
