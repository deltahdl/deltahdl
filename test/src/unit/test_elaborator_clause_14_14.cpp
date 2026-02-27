// §14.14: Global clocking

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Global clocking block declaration elaborates
TEST(ElabA611, GlobalClockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
