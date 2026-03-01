// §14.7: Clocking block scope and lifetime

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Clocking block within a program.
TEST(ParserSection19, ClockingBlock_InProgram) {
  EXPECT_TRUE(
      ParseOk("program test_prog(input clk, input [7:0] data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

// =============================================================================
// §4.6: Program block with clocking block reference
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithClockingBlock) {
  EXPECT_TRUE(
      ParseOk("program p(input logic clk);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output valid;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(\"synced\");\n"
              "  end\n"
              "endprogram\n"));
}

}  // namespace
