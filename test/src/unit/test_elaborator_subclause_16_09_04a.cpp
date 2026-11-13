#include <gtest/gtest.h>

#include <vector>

#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GlobalClockingSampledFunctions, RecognizesEveryProvidedFunction) {
  GlobalClockingSampledFunction fn{};
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$past_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kPastGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$rose_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kRoseGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$fell_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFellGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$stable_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kStableGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$changed_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kChangedGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$future_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFutureGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$rising_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kRisingGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$falling_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFallingGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$steady_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kSteadyGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$changing_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kChangingGclk);
}

TEST(GlobalClockingSampledFunctions, RejectsNonGclkNames) {
  EXPECT_FALSE(IsGlobalClockingSampledFunction("$past"));
  EXPECT_FALSE(IsGlobalClockingSampledFunction("$rose"));
}

TEST(GlobalClockingSampledFunctions, PartitionsPastAndFuture) {
  EXPECT_TRUE(
      IsGlobalClockingPastFunction(GlobalClockingSampledFunction::kRoseGclk));
  EXPECT_FALSE(
      IsGlobalClockingFutureFunction(GlobalClockingSampledFunction::kRoseGclk));
  EXPECT_TRUE(IsGlobalClockingFutureFunction(
      GlobalClockingSampledFunction::kRisingGclk));
  EXPECT_FALSE(
      IsGlobalClockingPastFunction(GlobalClockingSampledFunction::kRisingGclk));
}

TEST(GlobalClockingSampledFunctions, FutureFunctionsLimitedToAssertionExprs) {
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kPropertyExpr));
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kSequenceExpr));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kActionBlock));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kProceduralCode));
}

TEST(GlobalClockingSampledFunctions, PastFunctionsUsableInActionBlocks) {
  EXPECT_TRUE(GlobalClockingPastFunctionAllowedIn(
      GlobalClockingFunctionPlace::kActionBlock));
  EXPECT_TRUE(GlobalClockingPastFunctionAllowedIn(
      GlobalClockingFunctionPlace::kProceduralCode));
}

TEST(GlobalClockingSampledFunctions, FutureFunctionsMayNotNest) {
  EXPECT_TRUE(GlobalClockingFutureFunctionNestingAllowed(false));
  EXPECT_FALSE(GlobalClockingFutureFunctionNestingAllowed(true));
}

TEST(GlobalClockingSampledFunctions, FutureFunctionsRejectSequenceMatchItems) {
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(false));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(true));
}

TEST(GlobalClockingElab, GclkFunctionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking declaration in an enclosing scope", 4,
                            "16.9.4"));
}

TEST(GlobalClockingElab, GclkFunctionWithGlobalClockingIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(GlobalClockingElab, FutureFunctionInProceduralCodeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  always @(posedge clk) x = $future_gclk(y);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only in a property or sequence expression", 5,
                            "16.9.4"));
}

TEST(GlobalClockingElab, GclkFunctionResolvesGlobalClockingFromParentInstance) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(GlobalClockingElab,
     GclkFunctionInAForkStatementWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial fork\n"
      "    x = $past_gclk(x);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAForInitializerWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = $past_gclk(x); i < 1; i = i + 1)\n"
      "      x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab, GclkFunctionInAForStepWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $past_gclk(x))\n"
      "      x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAnAssertionPassStatementWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAnAssertionFailStatementWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandcaseItemWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial randcase 1: x = $past_gclk(x); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceCodeBlockWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = $past_gclk(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInADelayControlWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial #($past_gclk(x)) x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

TEST(GlobalClockingElab, GclkFunctionInACycleDelayWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  initial ##($past_gclk(x)) x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARepeatEventCountWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  initial x <= repeat ($past_gclk(x)) @(posedge clk) 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAVariableInitializerWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    static int i = $past_gclk(x);\n"
      "    x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAVariableUnpackedDimensionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    logic [31:0] y [$past_gclk(x)];\n"
      "    y[0] = 32'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAnEventControlIffConditionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  initial @(posedge clk iff $past_gclk(x)) x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandcaseWeightWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial randcase $past_gclk(x): x = 32'd1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInACaseItemExpressionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial case (x) $past_gclk(x): x = 32'd1; default: x = 32'd0; "
      "endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceWeightWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := ($past_gclk(x));\n"
      "      a : { x = 32'd1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandJoinExpressionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join ($past_gclk(x)) a b;\n"
      "      a : { x = 32'd1; };\n"
      "      b : { x = 32'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceProductionArgumentWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a($past_gclk(x));\n"
      "      a( int v ) : { x = v; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceIfConditionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if ($past_gclk(x)) a else b;\n"
      "      a : { x = 32'd1; };\n"
      "      b : { x = 32'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceRepeatCountWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat ($past_gclk(x)) a;\n"
      "      a : { x = 32'd1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceCaseExpressionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case ($past_gclk(x)) 0: a; default: b; endcase;\n"
      "      a : { x = 32'd1; };\n"
      "      b : { x = 32'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceCaseItemExpressionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (x) $past_gclk(x): a; default: b; endcase;\n"
      "      a : { x = 32'd1; };\n"
      "      b : { x = 32'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAnAlwaysIffConditionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk iff $past_gclk(x)) x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAPropertyTreeWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  assert property (@(posedge clk) $past_gclk(a) |=> b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

TEST(GlobalClockingElab, GclkFunctionInASequenceWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  assert property (@(posedge clk) $rising_gclk(a) ##1 b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

TEST(GlobalClockingElab, GclkFunctionsInATreeAndASequenceAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  assert property (@(posedge clk) $past_gclk(a) |=> b);\n"
      "  assert property (@(posedge clk) $rising_gclk(a) ##1 b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(GlobalClockingElab, TheProcessOfAFutureAssertionCarriesTheGlobalEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, clk2, a, b;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  a1: assert property (@(posedge clk) $rising_gclk(a) |=> b);\n"
      "  a2: assert property (@(posedge clk) $rising_gclk(a) ##1 b);\n"
      "  a3: assert property (@(posedge clk) a |=> b);\n"
      "  a4: assert property (@(posedge clk) $rising_gclk(a) |=>\n"
      "        @(posedge clk2) b);\n"
      "  a5: assert property (@(posedge clk) $rising_gclk(a) ##1\n"
      "        @(posedge clk2) b |=> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  std::vector<bool> carries;
  for (const RtlirProcess& p : design->top_modules[0]->processes) {
    if (p.is_concurrent_clocked)
      carries.push_back(!p.gclk_future_event.empty());
  }
  EXPECT_EQ(carries, (std::vector<bool>{true, true, false, true, true}));
}

TEST(GlobalClockingElab, FutureGclkFunctionInAnAlwaysIffConditionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk iff $future_gclk(x)) x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only in a property or sequence expression", 4,
                            "16.9.4"));
}

TEST(GlobalClockingElab,
     FutureFunctionInAConcurrentAssertionPropertyIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  assert property (@(posedge clk) $rising_gclk(x));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(GlobalClockingElab, FutureFunctionInAnAssertionActionBlockErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  assert property (@(posedge clk) x) y = $future_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only in a property or sequence expression", 5,
                            "16.9.4"));
}

TEST(GlobalClockingFutureRules, ANestedFutureFunctionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  a1: assert property (@(posedge clk) $future_gclk(a || "
      "$rising_gclk(b)));\n"
      "  a2: assert property (@(posedge clk) $future_gclk(a || b));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a global clocking future sampled value function may not stand in the "
      "argument of $future_gclk";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.9.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.9.4"));
}

TEST(GlobalClockingFutureRules, AFutureFunctionBesideAMatchItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  sequence s;\n"
      "    bit v;\n"
      "    (a, v = a) ##1 (b == v)[->1];\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) s |=> $future_gclk(c));\n"
      "  a2: assert property (@(posedge clk) t ##1 t |=> $future_gclk(c));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a global clocking future sampled value function may not stand in an "
      "assertion that holds a sequence match item";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.9.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 12, "16.9.4"));
}

}  // namespace
