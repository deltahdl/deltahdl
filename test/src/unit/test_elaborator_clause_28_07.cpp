// §28.7

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GateElaboration, MosSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, ctrl;\n"
      "  nmos n1(out, data, ctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
