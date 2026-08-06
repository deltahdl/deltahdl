#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ContinuousAssignElab, Delay3OnVariableIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  assign #(1, 2, 3) v = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ContinuousAssignElab, SingleDelayOnVariableIsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  assign #5 v = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VectoredOrScalaredPackedDim, VectoredRequiresPackedDim) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire vectored w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VectoredOrScalaredPackedDim, ScalaredRequiresPackedDim) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire scalared w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VectoredOrScalaredPackedDim, VectoredWithPackedDimOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire vectored [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
