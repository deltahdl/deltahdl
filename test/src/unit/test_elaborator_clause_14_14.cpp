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

}  // namespace
