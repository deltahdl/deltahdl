#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Annex D.6: invoked with no argument, $list lists the object that is the
// current scope setting. With no prior $scope the current scope is the first
// top-level module, so that is what gets listed.
TEST(OptionalListSim, NoArgumentListsCurrentScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $list;\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastListedScope(), "t");
}

// Annex D.6: with no argument the listing follows the current scope setting, so
// a preceding $scope call changes which object $list reports.
TEST(OptionalListSim, NoArgumentFollowsInteractiveScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t.blk);\n"
      "    $list;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastListedScope(), "t.blk");
}

// Annex D.6: when an argument is supplied it shall refer to a specific module,
// task, function, or named block, and that named object is the one listed --
// independent of the current scope setting.
TEST(OptionalListSim, ArgumentListsSpecificScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $list(t.blk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastListedScope(), "t.blk");
}

// Annex D.6: the argument is a complete hierarchical name and may descend
// several levels to reach a block nested inside another named block.
TEST(OptionalListSim, ArgumentAcceptsMultiLevelHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      $list(t.outer.inner);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastListedScope(), "t.outer.inner");
}

// Annex D.6: an explicit argument overrides the current scope setting -- a
// $list with an argument lists the named scope even after a different $scope.
TEST(OptionalListSim, ArgumentOverridesCurrentScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t.blk);\n"
      "    $list(t);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastListedScope(), "t");
}

// Annex D.6: each $list produces a fresh listing, so when several are issued
// the scope most recently listed is the one observed.
TEST(OptionalListSim, MostRecentListingWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $list(t);\n"
      "    $list(t.blk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastListedScope(), "t.blk");
}

// Annex D.6: an argument "shall refer to a specific module, task, function,
// or named block", so one naming none of those, a scope the design has not
// got or a variable of it, is reported under D.6 at the argument and lists
// nothing: the scope last listed is the one the earlier call selected.
TEST(OptionalListSim, AnArgumentNamingNoScopeIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin : blk\n"
      "    $list(t.blk);\n"
      "    $list(t.nope);\n"
      "    $list(t.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$list takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.nope' is none",
                            5, "D.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$list takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.v' is none",
                            6, "D.6"));
  EXPECT_EQ(f.ctx.LastListedScope(), "t.blk");
}

// Annex D.6: the argument may name a task, a function, or an instance, each
// of which is among the objects "it shall refer to".
TEST(OptionalListSim, ArgumentAcceptsAnInstanceATaskAndAFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  task tk; endtask\n"
      "  function int fn; return 1; endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u1();\n"
      "  initial begin\n"
      "    $list(t.u1);\n"
      "    $list(t.u1.tk);\n"
      "    $list(t.u1.fn);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.ctx.LastListedScope(), "t.u1.fn");
}

}  // namespace
