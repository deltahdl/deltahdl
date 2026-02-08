add_library(deltahdl_lib STATIC
    common/types.cpp
    common/diagnostic.cpp
    common/source_mgr.cpp
    preprocessor/macro_table.cpp
    preprocessor/preprocessor.cpp
    lexer/keywords.cpp
    lexer/lexer.cpp
    parser/parser.cpp
    parser/expr_parser.cpp
    elaboration/elaborator.cpp
    elaboration/type_eval.cpp
    elaboration/const_eval.cpp
    simulation/scheduler.cpp
    simulation/process.cpp
    simulation/net.cpp
    simulation/variable.cpp
    simulation/systask.cpp
    simulation/vcd_writer.cpp
    synthesis/aig.cpp
    synthesis/synth_lower.cpp
    synthesis/aig_rewrite.cpp
    synthesis/aig_refactor.cpp
    synthesis/aig_balance.cpp
    synthesis/lut_map.cpp
    synthesis/cell_map.cpp
    synthesis/liberty.cpp
    synthesis/netlist_writer.cpp
    vpi/vpi_stub.cpp
)

target_include_directories(deltahdl_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(deltahdl main.cpp)
target_link_libraries(deltahdl PRIVATE deltahdl_lib)
