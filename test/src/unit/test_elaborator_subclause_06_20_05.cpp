#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(SpecparamElaboration, SpecparamReferencedByParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  parameter p = delay + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tRISE") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, LocalparamReferencingSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = delay + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

TEST(SpecparamElaboration, SpecparamNotInParameterList) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tRISE = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    EXPECT_NE(p.name, "tRISE");
  }
}

TEST(SpecparamElaboration, SpecparamReferencingPriorSpecparamSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tBase = 10;\n"
      "  specparam tDerived = tBase + 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecparamElaboration, SpecparamOutsideSpecifyCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tPD = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tPD") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// A specify parameter is a constant, so the report is the one §6.20 states for
// an assignment to any constant rather than a specparam-specific one.
TEST(SpecparamElaboration, AssignmentToSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  initial delay = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to constant 'delay'", 3, "6.20"));
}

TEST(SpecparamElaboration, NonblockingAssignmentToSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  initial delay <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to constant 'delay'", 3, "6.20"));
}

TEST(SpecparamElaboration, SpecparamInDeclarationRangeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam width = 8;\n"
      "  logic [width-1:0] data;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "specparam 'width' may not appear in a declaration "
                            "range specification",
                            3, "6.20.5"));
}

TEST(SpecparamElaboration, ParameterInDeclarationRangeSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  parameter width = 8;\n"
      "  logic [width-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecparamElaboration, SpecparamRangeWidthFromDeclaration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam [7:0] tDELAY = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tDELAY") {
      found = true;
      EXPECT_EQ(v.width, 8u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamNoRangeDefaultsToFinalValueWidth) {
  // §6.20.5: a specify parameter declared with no range specification takes the
  // range of its final value. An unsized integer constant is 32 bits wide, so
  // the elaborated specparam variable is 32 bits. This is the no-range
  // counterpart to SpecparamRangeWidthFromDeclaration, where an explicit [7:0]
  // range instead fixes the width at 8.
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tPD = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tPD") {
      found = true;
      EXPECT_EQ(v.width, 32u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamNoRangeTakesSizedLiteralWidth) {
  // §6.20.5: with no range specification, a specparam takes the range of its
  // final value. A sized integer literal fixes that width, so a 4-bit literal
  // yields a 4-bit variable — distinct from the 32-bit default an unsized
  // literal produces (SpecparamNoRangeDefaultsToFinalValueWidth).
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tW = 4'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tW") {
      found = true;
      EXPECT_EQ(v.width, 4u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamAssignedFromParameterSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  specparam tX = P + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tX") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(SpecparamElaboration, SpecparamAssignedFromLocalparamSucceeds) {
  // §6.20.5 / Table 6-11: a specify parameter may be assigned a constant
  // expression built from parameter constants. A localparam (§6.20.4) is such a
  // constant, and it is a distinct constant-expression input form from an
  // ordinary parameter, so the specparam initializer is exercised over a real
  // localparam declaration driven through parse + elaborate.
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam L = 4;\n"
      "  specparam tX = L + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tX") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// The seven cases below reach a specparam through a child link of Expr other
// than lhs and rhs. §6.20.5 forbids a parameter or localparam assigned a
// constant expression that includes a specify parameter, and forbids a
// specparam in the range specification of a declaration, whatever expression
// form the reference is written in. Each case names the link it covers, so a
// walk that stops following one of them fails exactly that case.

// Covers Expr::condition.
TEST(SpecparamElaboration, SpecparamInAParameterConditionalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = delay ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

// Covers Expr::args.
TEST(SpecparamElaboration, SpecparamInAParameterCallArgumentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  function int f(int a); return a + 1; endfunction\n"
      "  localparam lp = f(delay);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 4,
                            "6.20.5"));
}

// Covers Expr::elements.
TEST(SpecparamElaboration, SpecparamInAParameterConcatenationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = {delay, 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

// Covers Expr::repeat_count.
TEST(SpecparamElaboration, SpecparamAsAParameterReplicationCountIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  localparam lp = {delay{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 3,
                            "6.20.5"));
}

// Covers Expr::index, and Expr::base with it. `arr` is declared [63:0] so that
// bit 50 is within it and Elaborator::ValidatePartSelectBounds has nothing to
// report, leaving §6.20.5 the only rule the source breaks.
TEST(SpecparamElaboration, SpecparamAsAParameterIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  logic [63:0] arr;\n"
      "  localparam lp = arr[delay];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter references specparam 'delay'", 4,
                            "6.20.5"));
}

// Covers Expr::args reached from a declaration range, which is the second of
// the two §6.20.5 rules and the other caller of the walk, so the message and
// the location are those of CheckSpecparamInRange rather than of
// Elaborator::ValidateSpecparamInParams.
TEST(SpecparamElaboration, SpecparamInADeclarationRangeCallIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam width = 8;\n"
      "  function int f(int a); return a; endfunction\n"
      "  logic [f(width)-1:0] data;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "specparam 'width' may not appear in a declaration "
                            "range specification",
                            4, "6.20.5"));
}

// An ordinary parameter in the conditional the first case above rejects. What
// §6.20.5 forbids is a specify parameter, so a walk that reports every
// identifier it reaches through a newly followed link fails here.
TEST(SpecparamElaboration, ParameterInAConditionalStillSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  parameter width = 8;\n"
      "  localparam lp = width ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
