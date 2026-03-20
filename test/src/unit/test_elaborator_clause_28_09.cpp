// §28.9

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GateElaboration, CmosSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
