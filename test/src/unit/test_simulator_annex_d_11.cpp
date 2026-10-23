#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "helpers_event_callbacks.h"
#include "helpers_reported_error.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

// Annex D.11: before any $scope runs, the interactive scope is the first
// top-level module of the design.
TEST(OptionalScopeSim, InitialScopeIsFirstTopModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t");
}

// Annex D.11: the argument is a complete hierarchical name; a dotted name that
// reaches a named block is recorded in full.
TEST(OptionalScopeSim, ScopeAcceptsHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t.blk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.blk");
}

// Annex D.11: a complete hierarchical name may descend several levels. $scope
// records every component, so a name reaching a block nested inside another
// named block is captured in full.
TEST(OptionalScopeSim, ScopeAcceptsMultiLevelHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      $scope(t.outer.inner);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.outer.inner");
}

// Annex D.11: $scope specifies a single level of hierarchy, so the most recent
// call determines the current interactive scope.
TEST(OptionalScopeSim, LastScopeWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t);\n"
      "    $scope(t.blk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.blk");
}

// Annex D.11: the argument must give the full hierarchical name of a module, a
// task, a function or a named block. An instance under the top, a task of the
// top and a function of the instance are each such a name, and the last call's
// scope is the one that stands.
TEST(OptionalScopeSim, ScopeAcceptsAnInstanceATaskAndAFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  function int f; return 1; endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  sub u1();\n"
      "  task tk; endtask\n"
      "  initial begin\n"
      "    $scope(t.u1);\n"
      "    $scope(t.tk);\n"
      "    $scope(t.u1.f);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.u1.f");
}

// A named fork is a named block as a named begin-end is.
TEST(OptionalScopeSim, ScopeAcceptsANamedFork) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial fork : fk\n"
      "    $scope(t.fk);\n"
      "  join\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.fk");
}

// Annex D.11 with §9.3.5: a label on a statement other than a begin-end or a
// fork opens a named begin-end around the statement, a named block whose full
// name $scope takes.
TEST(OptionalScopeSim, ScopeAcceptsTheBeginALabelOpensAroundAStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    lbl: x = 1;\n"
      "    $scope(t.lbl);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.lbl");
}

// §9.3.5: a label on a foreach loop names the implicit block the loop
// creates, which $scope takes as it takes any named block.
TEST(OptionalScopeSim, ScopeAcceptsTheBlockALabelNamesOnAForeachLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[2];\n"
      "  initial begin\n"
      "    lp: foreach (a[i]) a[i] = i;\n"
      "    $scope(t.lp);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.lp");
}

// §9.3.5 opens a begin-end only around a procedural statement: the label of a
// concurrent assertion written as a module item names the assertion, which is
// none of the scopes $scope takes.
TEST(OptionalScopeSim, AConcurrentAssertionItemsLabelNamesNoScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0, x = 1;\n"
      "  a1: assert property (@(posedge clk) x);\n"
      "  initial $scope(t.a1);\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$scope takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.a1' is none",
                            4, "D.11"));
  EXPECT_EQ(f.ctx.InteractiveScope(), "t");
}

// An argument that names no scope of the design -- a name nothing declares,
// and a variable's -- is reported under D.11 and the scope stays where it
// was. Any text was recorded as the scope.
TEST(OptionalScopeSim, AnArgumentNamingNoScopeIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    $scope(t.nope);\n"
      "    $scope(t.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$scope takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.nope' is none",
                            4, "D.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$scope takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.v' is none",
                            5, "D.11"));
  EXPECT_EQ(f.ctx.InteractiveScope(), "t");
}

// Annex D.11 with §9.3.5: a label on an assertion written in a procedure opens
// a named begin around it, whose full name the assertion shares. $scope given
// that name makes the begin, a named block, the interactive scope, so the
// cbInteractiveScopeChange callback (§38.36.3) is given the begin rather than
// the assertion it holds.
TEST_F(EventCallbacksOfARun, ScopeOnALabelledAssertionNotesItsBegin) {
  Armer() = [] { PlaceEventCallback(cbInteractiveScopeChange, nullptr); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic clk = 0, x = 1;\n"
      "  always @(posedge clk) begin\n"
      "    i1: assert (x) else begin end\n"
      "  end\n"
      "  initial begin $arm; #1 $scope(top.i1); end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges =
      DeliveriesOf(cbInteractiveScopeChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].obj_type, vpiNamedBegin);
  EXPECT_EQ(kChanges[0].obj, "i1");
}

}  // namespace
