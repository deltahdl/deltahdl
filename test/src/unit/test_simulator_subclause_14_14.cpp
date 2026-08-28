#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GlobalClockingSim, SetAndGetGlobalClocking) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetGlobalClocking().empty());

  ClockingBlock block;
  block.name = "gclk";
  block.clock_signal = "clk_global";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  block.is_global = true;
  cmgr.Register(block);

  cmgr.SetGlobalClocking("gclk");
  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");

  const auto* found = cmgr.Find("gclk");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_global);
}

TEST(GlobalClockingSim, GlobalAndDefaultCoexist) {
  ClockingManager cmgr;

  ClockingBlock gblock;
  gblock.name = "gclk";
  gblock.clock_signal = "sys_clk";
  gblock.clock_edge = Edge::kPosedge;
  gblock.is_global = true;
  cmgr.Register(gblock);
  cmgr.SetGlobalClocking("gclk");

  ClockingBlock dblock;
  dblock.name = "dclk";
  dblock.clock_signal = "bus_clk";
  dblock.clock_edge = Edge::kPosedge;
  cmgr.Register(dblock);
  cmgr.SetDefaultClocking("dclk");

  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "dclk");
  EXPECT_NE(cmgr.Find("gclk"), nullptr);
  EXPECT_NE(cmgr.Find("dclk"), nullptr);
}

// §14.14: "The $global_clock system function shall be used to explicitly refer
// to the event expression in the effective global clocking declaration", and
// its lookup rule a) resolves that reference against the global clocking
// declaration in the enclosing module instance. The three cases below
// elaborate, lower and run the design, because acceptance is not what §14.14
// requires: the cases in test/src/unit/test_elaborator_subclause_14_14.cpp
// stop at elaboration, where a process that arms no watcher and stays
// suspended at @($global_clock) for the whole run looks exactly like one that
// resumes on every clocking event. Only a value the process wrote separates
// the two, so each case here drives the declared clock and reads that value
// back.
//
// The declaration is on `posedge clk` and the run drives three rises (t=5,
// t=15, t=25) with two falls between them, so the body runs three times. `clk`
// takes its starting level from its declaration rather than from a process, so
// the run contains no transition out of x and the rises above are every posedge
// there is.
TEST(GlobalClockingSim, EveryDeclaredPosedgeRunsTheGlobalClockEventBody) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

// §14.14 makes $global_clock the event expression of the effective global
// clocking declaration, so the edge it fires on is the edge that declaration
// names. Here that is `negedge clk`, and the run drives three falls (t=5, t=15,
// t=25) against two rises (t=10, t=20). Three is therefore the count only a
// process following the declared edge reaches: one that fires on the rises
// instead leaves hits at 2, and the case above cannot tell those apart because
// its declaration names posedge.
TEST(GlobalClockingSim, NegedgeDeclarationMakesGlobalClockFireOnFallsOnly) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b1;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(negedge clk); endclocking\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

// §14.14 states where $global_clock refers, not where it may be written, so it
// stands in any event control rather than only in the sensitivity list of an
// always. Here it is the event control of a statement in an initial block: the
// rise at t=5 is the clocking event of the declaration found by rule a), and
// the process resumes there and writes done. `done` starts at 0, so a run that
// never resumes the process reads back 0 rather than x.
TEST(GlobalClockingSim, GlobalClockInAnInitialEventControlResumesThatProcess) {
  SimFixture f;
  auto* done = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic done = 1'b0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial @($global_clock) done = 1'b1;\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "done");
  ASSERT_NE(done, nullptr);
  EXPECT_EQ(done->value.ToUint64(), 1u);
}

// §14.14 puts no condition on where the reference to the effective global
// clocking declaration's event expression stands, so an event control naming
// $global_clock resolves in the pass and fail statements of an immediate
// assertion's action block (§16.3) and in the statement of a randcase item
// (§18.16) exactly as it does in the sensitivity list of an always. Each of the
// three cases below drives one posedge of the declared clock and reads `hits`
// back: a process that resumed on that edge leaves 1, and one that arms no
// watcher and stays suspended at @($global_clock) for the whole run leaves the
// 0 the declaration gave it. The assertion cases hold the expression in a
// variable rather than writing a constant, so the branch each takes is the one
// the run evaluated.
TEST(GlobalClockingSim,
     GlobalClockInAnAssertionFailStatementResumesThatProcess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic ok = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial assert (ok) else @($global_clock) hits = hits + 1;\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingSim,
     GlobalClockInAnAssertionPassStatementResumesThatProcess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic ok = 1'b1;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial assert (ok) @($global_clock) hits = hits + 1;\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

// The randcase has one item, so §18.16's weighted draw selects that item on
// every run and the case reads the event control rather than the selection.
TEST(GlobalClockingSim, GlobalClockInARandcaseItemResumesThatProcess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial randcase 1: @($global_clock) hits = hits + 1; endcase\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

// §14.14 lookup rule b): a $global_clock reference in a scope that declares no
// global clocking of its own resolves against "a global clocking declaration in
// the parent module, interface, or checker instance scope of the enclosing
// instantiation". The three cases below run the design, because the elaborator
// cases in test/src/unit/test_elaborator_subclause_14_14.cpp assert only that
// such a source is accepted, and a process that arms no watcher and stays
// suspended at @($global_clock) for the whole run is accepted too.
//
// The declaration is in an instantiated child rather than in the top module,
// which is the shape §14.14's own example uses. The three cases at the end of
// this file put the declaration in the top module instead.

// §14.14's example has `common_sub` declare no global clocking and instantiate
// under `subsystem1`, whose declaration is the one its $global_clock resolves
// to. `subclk1` rises three times (t=5, t=15, t=25) against two falls, so a
// child following its ancestor's declaration counts three. A child resolving
// against nothing counts the 0 its declaration gave it.
TEST(GlobalClockingSim, GlobalClockInAChildFollowsItsAncestorsDeclaration) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module common_sub;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "endmodule\n"
      "module subsystem1;\n"
      "  logic subclk1 = 1'b0;\n"
      "  global clocking sub_sys1 @(posedge subclk1); endclocking\n"
      "  common_sub common();\n"
      "  initial begin\n"
      "    #5 subclk1 = 1'b1;\n"
      "    #5 subclk1 = 1'b0;\n"
      "    #5 subclk1 = 1'b1;\n"
      "    #5 subclk1 = 1'b0;\n"
      "    #5 subclk1 = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  subsystem1 sub1();\n"
      "endmodule\n",
      f, "sub1.common.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

// §14.14's worked example: `top.sub1.common` resolves to `top.sub1.sub_sys1`
// and `top.sub2.common` to `top.sub2.sub_sys2`, two declarations on two
// different signals reached from one `common_sub` module. `subclk1` rises once
// and `subclk2` twice, so the two instances of that module separate only where
// each followed the declaration of its own ancestor. A resolution that takes
// the first or the outermost declaration it finds gives both instances one
// count, and so does one that substitutes onto the shared ModuleDecl rather
// than onto each instance's own process.
TEST(GlobalClockingSim,
     SiblingInstancesEachFollowTheirOwnAncestorsDeclaration) {
  SimFixture f;
  const std::string kSrc =
      "module common_sub;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "endmodule\n"
      "module subsystem1;\n"
      "  logic subclk1 = 1'b0;\n"
      "  global clocking sub_sys1 @(posedge subclk1); endclocking\n"
      "  common_sub common();\n"
      "  initial #5 subclk1 = 1'b1;\n"
      "endmodule\n"
      "module subsystem2;\n"
      "  logic subclk2 = 1'b0;\n"
      "  global clocking sub_sys2 @(posedge subclk2); endclocking\n"
      "  common_sub common();\n"
      "  initial begin\n"
      "    #5 subclk2 = 1'b1;\n"
      "    #5 subclk2 = 1'b0;\n"
      "    #5 subclk2 = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  subsystem1 sub1();\n"
      "  subsystem2 sub2();\n"
      "endmodule\n";
  auto* first = RunAndFindVar(kSrc, f, "sub1.common.hits");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 1u);
  auto* second = f.ctx.FindVariable("sub2.common.hits");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->value.ToUint64(), 2u);
}

// §14.14 runs rule a) before rule b), so a scope that declares a global
// clocking of its own resolves against that one and never climbs. `ownclk`
// rises twice and `topclk` three times, so the count says which of the two
// declarations the child followed.
TEST(GlobalClockingSim, AChildsOwnGlobalClockingBeatsItsAncestors) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic ownclk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking own_gclk @(posedge ownclk); endclocking\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #10 ownclk = 1'b1;\n"
      "    #10 ownclk = 1'b0;\n"
      "    #10 ownclk = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic topclk = 1'b0;\n"
      "  global clocking top_gclk @(posedge topclk); endclocking\n"
      "  child c();\n"
      "  initial begin\n"
      "    #3 topclk = 1'b1;\n"
      "    #3 topclk = 1'b0;\n"
      "    #3 topclk = 1'b1;\n"
      "    #3 topclk = 1'b0;\n"
      "    #3 topclk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

// §14.14 with the global clocking declared in the top-level hierarchy block
// rather than in an instantiated child. Rule b) states no exception for that
// block: it is the scope the climb stops at, so a declaration there is the
// effective one for every reference below that finds no nearer declaration of
// its own, and the result is still "the event expression of that global
// clocking declaration" -- the top's own signal.
//
// The top-level hierarchy block is not an instance and has no instance name to
// reach its signals through, so the name written for a reference below it is
// §23.6's `$root.clk`, absolute from the top of the instantiated design. The
// first two cases below are that rule-b) reference; the third holds rule a)
// where it was, in the top module that declares the global clocking.
//
// Each of the three declares a `clk` in the child as well as in the top, so a
// reference resolved against the referencing scope rather than the declaring
// one finds a signal by that name and waits on the wrong one.

// The child's own `clk` is never driven, so a reference bound to it waits for
// an edge that never arrives and leaves `hits` at the 0 its declaration gave
// it. The top's `clk` rises three times (t=5, t=15, t=25) against two falls.
TEST(GlobalClockingSim, TopLevelGlobalClockingReachesAReferenceInAChild) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  child c();\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

// The child's own `clk` moves here, on a schedule of its own: it rises at t=7
// and t=21 while the top's rises at t=5, t=15 and t=25. Three is therefore the
// count only a reference following the top's declaration reaches, and a
// reference bound to the child's own `clk` reads back 2 rather than the 0 the
// case above leaves it at. Without this case a resolution that waits on any
// moving signal of that name passes.
TEST(GlobalClockingSim,
     ChildFollowsTheTopsGlobalClockNotItsOwnLikeNamedSignal) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #7 clk = 1'b1;\n"
      "    #7 clk = 1'b0;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  child c();\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

// §14.14 rule a) runs first, and a reference in the top-level hierarchy block
// that declares the global clocking is answered by it: the event expression
// already names a signal of the scope holding the reference, so nothing is
// written onto it and no `$root` stands in front of it. The top's `clk` rises
// three times. A `$root.clk` written here anyway reads back 0 wherever the
// simulator does not resolve that spelling, which is what makes this case fail
// rather than merely repeat the rule-a) cases above.
TEST(GlobalClockingSim,
     ReferenceInTheDeclaringTopModuleStaysUnqualifiedAlongsideAChild) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic clk = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  child c();\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

}  // namespace
