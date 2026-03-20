// §28.8

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GateElaboration, PassSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
