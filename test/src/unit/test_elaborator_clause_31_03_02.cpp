// §31.3.2: $hold

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// $hold timing check elaborates
TEST(ElabA705, HoldTimingCheckElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
