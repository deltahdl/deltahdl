// §14.8: Multiple clocking blocks example

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Clocking block in a program with initial block accessing signals.
TEST(ParserSection19, ClockingBlockScope_ProgramAccess) {
  EXPECT_TRUE(
      ParseOk("program test_prog(\n"
              "  input phi1, input [15:0] data, output logic write,\n"
              "  input phi2, inout [8:1] cmd, input enable\n"
              ");\n"
              "  clocking cd1 @(posedge phi1);\n"
              "    input data;\n"
              "    output write;\n"
              "    input state = top.cpu1.state;\n"
              "  endclocking\n"
              "  clocking cd2 @(posedge phi2);\n"
              "    input #2 output #4ps cmd;\n"
              "    input enable;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cd1);\n"
              "  end\n"
              "endprogram\n"));
}

}  // namespace
