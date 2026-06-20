#include "fixture_simulator.h"

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

}  // namespace
