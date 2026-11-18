#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

int CountVariablesNamed(const RtlirModule* mod, char last) {
  int count = 0;
  for (const auto& var : mod->variables) {
    if (!var.name.empty() && var.name.back() == last) ++count;
  }
  return count;
}

TEST(GenerateConstructSyntax, ConstantConditionFromEnclosingScopeElaborates) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter P = 1;\n"
      "  if (P == 1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 1);
}

TEST(GenerateConstructSyntax, ConstantConditionFromLocalparamElaborates) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  localparam Q = 1;\n"
      "  if (Q == 1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 1);
}

TEST(GenerateConstructSyntax, NonConstantGenerateSchemeIsDiagnosed) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  logic v;\n"
      "  if (v) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.f.diag.Diagnostics(),
                            "generate-if condition is not constant", 3,
                            "27.5"));
}

TEST(GenerateConstructSyntax, NonConstantCaseSelectorIsDiagnosed) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  logic v;\n"
      "  case (v)\n"
      "    0: begin\n"
      "      logic a;\n"
      "    end\n"
      "    default: begin\n"
      "      logic b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.f.diag.Diagnostics(),
                            "generate-case selector is not constant", 3,
                            "27.5"));
}

TEST(GenerateConstructSyntax, FalseConditionYieldsZeroInstances) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (0) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 0);
}

TEST(GenerateConstructSyntax, LoopProducesMultipleInstances) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 3; i = i + 1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 3);
}

TEST(GenerateConstructSyntax, NonConstantCaseItemExpressionIsReported) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  logic v;\n"
      "  case (1)\n"
      "    v: begin : a logic x; end\n"
      "    default: begin : b logic y; end\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.f.diag.Diagnostics(),
                            "generate-case item expression is not constant", 4,
                            "27.3"));
}

TEST(GenerateConstructSyntax, NonConstantCaseItemAfterTheMatchIsReported) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  logic v;\n"
      "  case (1)\n"
      "    1: begin : a logic x; end\n"
      "    2, v: begin : b logic y; end\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.f.diag.Diagnostics(),
                            "generate-case item expression is not constant", 5,
                            "27.3"));
}

TEST(GenerateConstructSyntax, ConstantCaseItemExpressionsElaborate) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter P = 3;\n"
      "  case (P)\n"
      "    1, P - 1: begin logic b; end\n"
      "    2 + 1, 4: begin logic a; end\n"
      "    default: begin logic c; end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'b'), 0);
}

TEST(GenerateConstructSyntax, NonConstantSchemesOutsideAModuleAreReported) {
  auto r = RunGenerateElaboration(
      "interface ifc;\n"
      "  logic v;\n"
      "  if (v) begin : g logic a; end\n"
      "endinterface\n"
      "program pr;\n"
      "  logic v;\n"
      "  case (v) 1'b1: begin : g logic a; end default: ; endcase\n"
      "endprogram\n"
      "checker ck;\n"
      "  logic v;\n"
      "  for (genvar k = 0; k < v; k++) begin : g end\n"
      "endchecker\n"
      "module top; ifc i(); pr p(); ck c(); endmodule\n");
  const auto& diags = r.f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, "generate-if condition is not constant", 3, "27.5"));
  EXPECT_TRUE(ReportedError(diags, "generate-case selector is not constant", 7,
                            "27.5"));
  EXPECT_TRUE(ReportedError(
      diags, "generate-for termination expression is not constant", 11,
      "27.4"));
}

TEST(GenerateConstructSyntax, ANestedConditionOnABlockVariableIsNotConstant) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : v\n"
      "    logic z;\n"
      "    if (z) begin : w end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.f.diag.Diagnostics(),
                            "generate-if condition is not constant", 4,
                            "27.5"));
}

TEST(GenerateConstructSyntax, DISABLED_ANameInsideAnUnselectedBlockIsReported) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : u1 int v; end\n"
      "  else begin : u2 int w; end\n"
      "  if (0) begin : u3 int x; end\n"
      "  initial $display(\"%0d %0d\", u2.w, u3.x);\n"
      "endmodule\n");
  const auto& diags = r.f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "hierarchical name 'u2' resolves to no declaration", 5, "23.8"));
  EXPECT_TRUE(ReportedError(
      diags, "hierarchical name 'u3' resolves to no declaration", 5, "23.8"));
}

TEST(GenerateBlockEnumConstants, ASiblingBlockParameterCannotNameThem) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : g1\n"
      "    typedef enum {A, B} e_t;\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    localparam int P = B;\n"
      "  end\n"
      "  if (0) begin : h1 end\n"
      "  else begin : h2\n"
      "    typedef enum {C, D} f_t;\n"
      "  end\n"
      "  if (1) begin : h3\n"
      "    localparam int Q = D;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : k1 typedef enum {E, F} k_t; end\n"
      "    default: ;\n"
      "  endcase\n"
      "  if (1) begin : k2\n"
      "    localparam int R = F;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : l\n"
      "    typedef enum {G = i, H} l_t;\n"
      "  end\n"
      "  if (1) begin : k3\n"
      "    localparam int S = H;\n"
      "  end\n"
      "endmodule\n");
  const auto& diags = r.f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'P' initializer is not a constant expression", 6,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'Q' initializer is not a constant expression", 13,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'R' initializer is not a constant expression", 20,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'S' initializer is not a constant expression", 26,
      "6.20.4"));
}

TEST(GenerateBlockEnumConstants, ParametersOutsideTheBlockCannotNameThem) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : g\n"
      "    if (1) begin : n\n"
      "      typedef enum {A, B} e_t;\n"
      "    end\n"
      "    localparam int P = B;\n"
      "  end\n"
      "  localparam int Q = A;\n"
      "endmodule\n");
  const auto& diags = r.f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'P' initializer is not a constant expression", 6,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'Q' initializer is not a constant expression", 8,
      "6.20.4"));
}

TEST(GenerateBlockEnumConstants, EachBlockAndIterationDeclaresItsOwn) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : g1\n"
      "    typedef enum {A, B} e_t;\n"
      "    localparam int P = B;\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    typedef enum {B, A} e_t;\n"
      "    localparam int P = B;\n"
      "  end\n"
      "  for (genvar i = 0; i < 3; i++) begin : l\n"
      "    typedef enum {X = i, Y} h_t;\n"
      "    localparam int P = Y;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.f.has_errors);
  EXPECT_TRUE(r.f.diag.Diagnostics().empty());
}

TEST(GenerateBlockEnumConstants, AHierarchicalNameIsNotAConstant) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : g1\n"
      "    typedef enum {A, B} e_t;\n"
      "  end\n"
      "  localparam int Q = g1.B;\n"
      "  localparam int R = 1;\n"
      "endmodule\n");
  const auto& diags = r.f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "parameter 'Q' value contains a hierarchical reference", 5,
      "6.20.2"));
  EXPECT_FALSE(ReportedError(
      diags, "parameter 'R' value contains a hierarchical reference", 6,
      "6.20.2"));
}

}  // namespace
