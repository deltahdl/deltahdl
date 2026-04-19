// §28.9

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CmosSwitchElaboration, CmosElaboratesWithoutError) {
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

TEST(CmosSwitchElaboration, RcmosElaboratesWithoutError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A single cmos instance lowers to exactly one continuous assign driving the
// output from the ternary (ncontrol ? data : (pcontrol ? 'z : data)).
TEST(CmosSwitchElaboration, CmosEmitsSingleContinuousAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 1u);
}

TEST(CmosSwitchElaboration, RcmosEmitsSingleContinuousAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 1u);
}

}  // namespace
