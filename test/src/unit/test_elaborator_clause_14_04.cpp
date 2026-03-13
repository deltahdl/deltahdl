#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingSkewElab, SkewVariationsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1step data;\n"
      "    output negedge #1 ack;\n"
      "    input posedge ready;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingSkewElab, ExplicitZeroInputSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #0 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewElab, ExplicitZeroOutputSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #0 ack;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewElab, ParameterAsSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter SKEW = 3;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #SKEW data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewElab, InputOutputCombinedSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #5 output #6 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
