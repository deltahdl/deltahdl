include(FetchContent)
FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.15.2
)
FetchContent_MakeAvailable(googletest)

include(GoogleTest)

function(add_unit_test name)
    add_executable(${name} unit/${name}.cpp)
    target_link_libraries(${name} PRIVATE deltahdl_lib GTest::gtest_main)
    gtest_discover_tests(${name})
endfunction()

add_unit_test(test_logic4)
add_unit_test(test_lexer)
add_unit_test(test_parser)
add_unit_test(test_process)
add_unit_test(test_scheduler)
add_unit_test(test_aig)
