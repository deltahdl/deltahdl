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

// §10.3 Syntax 10-1: a continuous assignment's target is a net or variable
// lvalue, and an operator expression is neither.
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

// §10.3: a continuous assignment drives a net or a variable, and a parameter
// is a constant (§6.20), whether the target names it whole or as an element of
// a concatenation.
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

// §10.3 states its rules wherever a continuous assignment stands, and a
// generate block's items are module items (§27.3): the (highz0, highz1) pair,
// a non-constant select on the left-hand side, and a variable driven both by a
// continuous and by a procedural assignment.
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

// §6.5 with §27.3: a generate block's continuous assignment to a variable the
// module writes procedurally is as illegal as the module's own would be, and a
// genvar is a constant select index.
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
