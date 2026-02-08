add_library(deltahdl_lib STATIC
    common/types.cpp
    common/diagnostic.cpp
    common/source_mgr.cpp
    preprocessor/macro_table.cpp
    preprocessor/preprocessor.cpp
    lexer/keywords.cpp
    lexer/lexer.cpp
    parser/parser.cpp
    parser/parser_decl.cpp
    parser/parser_generate.cpp
    parser/parser_toplevel.cpp
    parser/expr_parser.cpp
    elaboration/elaborator.cpp
    elaboration/type_eval.cpp
    elaboration/const_eval.cpp
    elaboration/sensitivity.cpp
    simulation/scheduler.cpp
    simulation/process.cpp
    simulation/variable.cpp
    simulation/sim_context.cpp
    simulation/eval.cpp
    simulation/stmt_exec.cpp
    simulation/lowerer.cpp
    synthesis/aig.cpp
)

target_include_directories(deltahdl_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(deltahdl main.cpp)
target_link_libraries(deltahdl PRIVATE deltahdl_lib)
