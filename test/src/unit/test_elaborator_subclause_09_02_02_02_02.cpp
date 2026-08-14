

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombVsAlwaysStar, AlwaysStarIsAlwaysKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, y;\n"
      "  always @* y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlways);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarNoMultiDriverError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, y;\n"
      "  always @* y = a;\n"
      "  always @* y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsTimingControl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) a = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysCombRejectsTimingControl) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  always_comb #5 a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombExtendedSim, AlwaysCombConstAssignTime0) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] y;\n"
      "  always_comb y = 42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

TEST(AlwaysStarSim, AlwaysStarEquivAlwaysComb) {
  SimFixture f_star;
  auto* d_star = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_star);
  ASSERT_NE(d_star, nullptr);

  Lowerer lowerer_star(f_star.ctx, f_star.arena, f_star.diag);
  lowerer_star.Lower(d_star);
  f_star.scheduler.Run();

  SimFixture f_comb;
  auto* d_comb = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_comb);
  ASSERT_NE(d_comb, nullptr);

  Lowerer lowerer_comb(f_comb.ctx, f_comb.arena, f_comb.diag);
  lowerer_comb.Lower(d_comb);
  f_comb.scheduler.Run();

  auto* y_star = f_star.ctx.FindVariable("y");
  auto* y_comb = f_comb.ctx.FindVariable("y");
  ASSERT_NE(y_star, nullptr);
  ASSERT_NE(y_comb, nullptr);
  EXPECT_EQ(y_star->value.ToUint64(), y_comb->value.ToUint64());
}

TEST(AlwaysCombVsAlwaysStar, ForkJoinInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, EventControlInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_comb @(posedge clk) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not have an explicit event control", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, EmbeddedEventControlInAlwaysCombErrors) {
  // An event control can appear in two syntactic positions: as the
  // always_comb's own control (rejected via the block's sensitivity, see
  // EventControlInAlwaysCombErrors) or as a statement nested inside the body.
  // The body-embedded form reaches the statement-timing scan directly and must
  // be rejected just the same.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_comb begin\n"
      "    a = 1;\n"
      "    @(posedge clk) a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsEmbeddedEventControl) {
  // always @* imposes no such restriction, so the same body-embedded event
  // control is accepted — the permissive counterpart to the always_comb form.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always @* begin\n"
      "    a = 1;\n"
      "    @(posedge clk) a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, WaitInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic ready, a;\n"
      "  always_comb wait (ready) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, WaitForkInAlwaysCombErrors) {
  // 'wait fork' is a statement that blocks (a distinct AST node from a plain
  // wait), so always_comb must reject it just like other suspending forms.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    a = 1;\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsWaitFork) {
  // always @* places no such restriction, so the same wait fork is accepted.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always @* begin\n"
      "    a = 1;\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsForkJoin) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @* begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsWait) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic ready, a;\n"
      "  always @* wait (ready) a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, JoinAnyInAlwaysCombErrors) {
  // The §9.2.2.2.2 prohibition names "fork-join statements" as a category, so
  // it covers every join variant, not just plain join. fork...join_any parses
  // to the same kFork node (with a join_any join_kind), and always_comb must
  // reject it exactly as it rejects fork...join.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, JoinNoneInAlwaysCombErrors) {
  // fork...join_none is likewise a fork-join statement and is rejected in an
  // always_comb even though its join_none form does not itself suspend the
  // parent; the prohibition is categorical, not blocking-behavior based.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsJoinAny) {
  // always @* carries no fork-join restriction, so the same join_any block is
  // accepted — the accepting counterpart to the always_comb rejection.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @* begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsJoinNone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @* begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysCombRejectsNestedDelay) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    if (a)\n"
      "      #1 a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

// §9.2.2.2.2: "Statements in an always_comb shall not include those that block,
// have blocking timing or event controls, or fork-join statements." A cycle
// delay is a blocking timing control: §14.11 lists cycle_delay under
// procedural_timing_control and rules that "The cycle delay timing control
// shall wait for the specified number of clocking block events."
//
// The three cases below assert through ReportedError, as every rejection case
// in this file does, because any rejection satisfies a bare error flag
// -- including a rejection of the source before it ever reached the always_comb
// check. The line is the always_comb keyword's, which is where
// ValidateCombLatchProcess reports, and not the offending statement's.
//
// The run reports a second error this case does not name: §14.11 also rules
// that a ## with no default clocking in effect is an error, and this module
// declares no clocking block.
TEST(AlwaysCombVsAlwaysStar, CycleDelayInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    ##3 q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

// §9.2.2.2.2 forbids a statement that blocks, and §15.5.4 rules that "The
// wait_order construct suspends the calling process until all of the specified
// events are triggered in the given order". Its Syntax 15-2 is wait_order (
// hierarchical_identifier { , hierarchical_identifier } ) action_block, where
// action_block ::= statement_or_null, so the null action written here is the
// whole statement and the two arguments are declared events.
TEST(AlwaysCombVsAlwaysStar, WaitOrderInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  event a, b;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    wait_order(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 4,
                            "9.2.2.2.2"));
}

// §9.2.2.2.2 forbids a statement that blocks, and §16.17 rules that "The expect
// statement is a procedural blocking statement" which "causes the executing
// process to block until the given property succeeds or fails". Its Syntax
// 16-20 is expect ( property_spec ) action_block, and the property spec here
// carries the clocking event of the §16.17 example; the action block is the
// null one.
TEST(AlwaysCombVsAlwaysStar, ExpectInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, ready, q;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    expect (@(posedge clk) ready);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

// The boundary of the same rule. §9.2.2.2.2 reaches a statement that blocks,
// and §15.5.1 rules that with the ->> operator "the statement executes without
// blocking, and it creates a nonblocking assign update event", so a nonblocking
// event trigger is not one and an always_comb containing it stands.
//
// The claim is only that no error cites §9.2.2.2.2, so any other diagnostic the
// run records leaves it standing: this case is about which rule fired, not
// about how quiet the run was.
TEST(AlwaysCombVsAlwaysStar, NonblockingEventTriggerInAlwaysCombAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  event ev;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    ->> ev;\n"
      "  end\n"
      "endmodule\n",
      f);
  std::string cited;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError && diag.subclause == "9.2.2.2.2")
      cited = diag.message;
  }
  EXPECT_TRUE(cited.empty())
      << "an error cites §9.2.2.2.2 against a nonblocking event trigger, "
         "which §15.5.1 rules executes without blocking: "
      << cited;
}

}  // namespace
