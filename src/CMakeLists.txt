add_library(deltahdl_lib STATIC
    common/types.cpp
    common/diagnostic.cpp
    common/source_mgr.cpp
    preproc/macro_table.cpp
    preproc/preprocessor.cpp
    lexer/keywords.cpp
    lexer/lexer.cpp
    parser/parser.cpp
    parser/expr_parser.cpp
    elab/elaborator.cpp
    elab/type_eval.cpp
    elab/const_eval.cpp
    sim/scheduler.cpp
    sim/process.cpp
    sim/net.cpp
    sim/variable.cpp
    sim/systask.cpp
    sim/vcd_writer.cpp
    synth/aig.cpp
    synth/synth_lower.cpp
    synth/aig_rewrite.cpp
    synth/aig_refactor.cpp
    synth/aig_balance.cpp
    synth/lut_map.cpp
    synth/cell_map.cpp
    synth/liberty.cpp
    synth/netlist_writer.cpp
    vpi/vpi_stub.cpp
)

target_include_directories(deltahdl_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(deltahdl main.cpp)
target_link_libraries(deltahdl PRIVATE deltahdl_lib)
