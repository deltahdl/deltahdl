// §14.12: Default clocking

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Default clocking block declaration elaborates
TEST(ElabA611, DefaultClockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
