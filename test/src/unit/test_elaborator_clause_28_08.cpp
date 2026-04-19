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

TEST(GateElaboration, PassEnableSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Bidirectional pass switches must not lower to a continuous assignment —
// they have no unique driven terminal from which to drive the other.
TEST(GateElaboration, TranEmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, RtranEmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  rtran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Tranif0EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Rtranif0EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Rtranif1EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

}  // namespace
