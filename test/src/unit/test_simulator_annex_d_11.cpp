#include "fixture_simulator.h"

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

}
