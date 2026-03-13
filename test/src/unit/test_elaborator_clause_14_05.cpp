#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingHierExprElab, SimpleHierExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input sig = top.dut.sig;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingHierExprElab, ConcatenationExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking mem @(clock);\n"
             "    input instruction = { opcode, regA, regB[3:1] };\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, OutputHierExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output ack = top.dut.ack;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, InoutHierExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data = top.dut.data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, PartSelectExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input nibble = data[7:4];\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingHierExprElab, MixedSignalsWithHierExprsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input a, b = top.sig_b, c;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
