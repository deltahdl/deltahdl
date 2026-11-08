#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "helpers_event_callbacks.h"
#include "helpers_reported_error.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

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
