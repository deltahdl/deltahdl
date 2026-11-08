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

}  // namespace
