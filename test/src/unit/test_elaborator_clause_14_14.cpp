#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GlobalClockingElab, DuplicateGlobalClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithDeclarationIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
