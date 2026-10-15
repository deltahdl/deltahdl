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

// §27.3: the expressions in a generate scheme are constant expressions
// resolved against the enclosing scope (see §23.9). A generate-if whose
// condition is a module parameter elaborates cleanly and instantiates the
// selected block's declarations into the module.
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

// §27.3: a generate-scheme expression is a constant expression, which admits a
// localparam operand as well as a parameter. localparam resolution runs through
// a different declaration path than parameter, so a generate-if gated on a
// localparam is exercised on its own: the selected block's declaration reaches
// the module.
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

// §27.3: all expressions in generate schemes shall be constant expressions,
// deterministic at elaboration time. A condition that depends on a runtime
// variable is not constant, and the elaborator reports it as an error.
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

// §27.3: the constant-expression requirement covers every generate-scheme
// expression, including a case-generate selector. A selector that depends on
// a runtime variable is not constant and is reported as an error.
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

// §27.3: elaboration of a generate construct results in zero or more
// instances of a generate block. A false condition yields zero, so the
// block's declarations never reach the module.
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

// §27.3: a loop generate construct may produce more than one instance of its
// generate block; each iteration contributes its own copy of the block's
// declarations.
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

// §27.3: every expression of a generate scheme is a constant expression, and
// Syntax 27-1 writes each item expression of a case-generate as one. An item
// that reads a variable is reported where it stands, rather than read as an
// alternative that does not match, which would build the default block in its
// place with nothing said.
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

// The requirement holds of every item expression, not only of those read
// before the one that matches: here the first item selects its block, and the
// item after it still reads a variable. A check made while searching for the
// match stops at line 4 and never reaches line 5.
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

// Item expressions that fold are constant, so a case-generate built from them
// elaborates with no report, and the alternative listing the selector's value
// second builds its block.
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
