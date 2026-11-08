#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

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

TEST(ContinuousAssignElab, TargetThatIsNoLvalueIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic a, b, c;\n"
      "  assign a + b = c;\n"
      "  assign {a, b + c} = 2'b0;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "continuous assignment target is not a net or variable lvalue", line,
        "10.3"));
  }
}

TEST(ContinuousAssignElab, ParameterTargetIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  parameter P = 1;\n"
      "  logic a;\n"
      "  assign P = a;\n"
      "  assign {a, P} = 2'b0;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "continuous assignment to parameter 'P'", line,
                              "10.3"));
  }
}

TEST(ContinuousAssignElab, RulesReachGenerateBlockItems) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w; wire [3:0] v; int i; logic x;\n"
      "  if (1) begin : g\n"
      "    assign (highz0, highz1) w = 1'b0;\n"
      "    assign v[i] = 1'b1;\n"
      "    assign x = 1'b0;\n"
      "    initial x = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 4,
                            "28.3.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment left-hand side requires a "
                            "constant select expression",
                            5, "10.3.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'x' has both continuous and procedural "
                            "assignments",
                            7, "6.5"));
}

TEST(ContinuousAssignElab, GenerateDriverMeetsModuleProcedure) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic y; wire [1:0] n;\n"
      "  initial y = 1'b1;\n"
      "  for (genvar k = 0; k < 2; k++) begin : g\n"
      "    assign n[k] = 1'b0;\n"
      "  end\n"
      "  if (1) begin : h\n"
      "    assign y = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'y' has both continuous and procedural "
                            "assignments",
                            8, "6.5"));
  EXPECT_EQ(FindDiag(f, "constant select expression"), nullptr);
}

}  // namespace
