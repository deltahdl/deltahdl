#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MultiBlockExampleElab, ProgramWithTwoClockingBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("program p(\n"
             "  input phi1, input [15:0] data, output logic write,\n"
             "  input phi2, inout [8:1] cmd, input enable\n"
             ");\n"
             "  clocking cd1 @(posedge phi1);\n"
             "    input data;\n"
             "    output write;\n"
             "  endclocking\n"
             "  clocking cd2 @(posedge phi2);\n"
             "    input #2 output #4ps cmd;\n"
             "    input enable;\n"
             "  endclocking\n"
             "endprogram\n"));
}

TEST(MultiBlockExampleElab, ModuleWithTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cd1 @(posedge phi1);\n"
             "    input data;\n"
             "  endclocking\n"
             "  clocking cd2 @(posedge phi2);\n"
             "    output cmd;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(MultiBlockExampleElab, HierExprInMultiBlockElaborates) {
  EXPECT_TRUE(
      ElabOk("program p(input phi1);\n"
             "  clocking cd1 @(posedge phi1);\n"
             "    input state = top.cpu1.state;\n"
             "  endclocking\n"
             "endprogram\n"));
}

}  // namespace
