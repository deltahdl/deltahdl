#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  // §10.3.3 owns the multiple-delay rule; §10.3 has no report of its own here.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple delays not allowed on continuous "
                            "assignment to a variable",
                            3, "10.3.3"));
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
  // §6.9.2 owns this rule, not clause 10: vectored and scalared are advisory
  // keywords for vector net declarations, so one without a packed dimension
  // has no declaration to advise about.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "vectored or scalared requires at least one packed "
                            "dimension",
                            2, "6.9.2"));
}

TEST(VectoredOrScalaredPackedDim, ScalaredRequiresPackedDim) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire scalared w;\n"
      "endmodule\n",
      f);
  // §6.9.2, as above: the same site answers for both keywords.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "vectored or scalared requires at least one packed "
                            "dimension",
                            2, "6.9.2"));
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
