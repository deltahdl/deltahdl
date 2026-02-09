include(FetchContent)
FetchContent_Declare(
    googletest
    URL https://github.com/google/googletest/archive/refs/tags/v1.15.2.tar.gz
    URL_HASH SHA256=7b42b4d6ed48810c5362c265a17faebe90dc2373c885e5216439d37927f02926
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
add_unit_test(test_const_eval)
add_unit_test(test_driver_update)
add_unit_test(test_net)
add_unit_test(test_eval)
add_unit_test(test_lowerer)
add_unit_test(test_elaboration)
add_unit_test(test_preprocessor)
add_unit_test(test_vcd)
add_unit_test(test_synth_lower)
add_unit_test(test_aig_opt)
add_unit_test(test_lut_map)
add_unit_test(test_netlist_writer)
add_unit_test(test_adv_sim)
add_unit_test(test_vpi)
add_unit_test(test_adv_synth)
