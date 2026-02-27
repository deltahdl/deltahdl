// §14.5: Hierarchical expressions

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Clocking block with hierarchical expression elaborates
TEST(ElabA611, HierExprElaborates) {
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

}  // namespace
