include(FetchContent)
FetchContent_Declare(
    Catch2
    GIT_REPOSITORY https://github.com/catchorg/Catch2.git
    GIT_TAG v3.5.2
)
FetchContent_MakeAvailable(Catch2)

list(APPEND CMAKE_MODULE_PATH ${catch2_SOURCE_DIR}/extras)
include(Catch)

function(add_unit_test name)
    add_executable(${name} unit/${name}.cpp)
    target_link_libraries(${name} PRIVATE deltahdl_lib Catch2::Catch2WithMain)
    catch_discover_tests(${name})
endfunction()

add_unit_test(test_logic4)
add_unit_test(test_lexer)
add_unit_test(test_parser)
add_unit_test(test_process)
add_unit_test(test_scheduler)
add_unit_test(test_aig)
