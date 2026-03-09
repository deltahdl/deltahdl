#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

}
TEST(MultipleClockingBlocks, MultipleClockingBlocks) {
  auto r = Parse(
      "module m;\n"
      "  clocking cd1 @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  clocking cd2 @(posedge phi2);\n"
      "    output cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cb1 = FindClockingBlockByIndex(r, 0);
  auto* cb2 = FindClockingBlockByIndex(r, 1);
  ASSERT_NE(cb1, nullptr);
  ASSERT_NE(cb2, nullptr);
  EXPECT_EQ(cb1->name, "cd1");
  EXPECT_EQ(cb2->name, "cd2");
}
