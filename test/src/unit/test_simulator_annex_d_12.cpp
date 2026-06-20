#include "fixture_simulator.h"

using namespace delta;

namespace {

// Annex D.12: $showscopes lists the modules, tasks, functions, and named blocks
// defined at the current scope level. The scope it operates on is the current
// interactive scope, which starts as the first top-level module.
TEST(OptionalShowScopesSim, ShowsCurrentScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $showscopes;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastShownScope(), "t");
}

// Annex D.12: with no argument the listing is restricted to objects at the
// current scope level only (not recursive).
TEST(OptionalShowScopesSim, NoArgumentIsNotRecursive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $showscopes;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.ShowScopesRecursive());
}

// Annex D.12: a zero argument value also restricts the listing to the current
// scope level only.
TEST(OptionalShowScopesSim, ZeroArgumentIsNotRecursive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $showscopes(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.ShowScopesRecursive());
}

// Annex D.12: a nonzero argument value lists every object in or below the
// current hierarchical scope.
TEST(OptionalShowScopesSim, NonzeroArgumentIsRecursive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $showscopes(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.ShowScopesRecursive());
}

// Annex D.12: $showscopes operates on the current scope, so retargeting the
// interactive scope with $scope (Annex D.11) changes which scope is shown.
TEST(OptionalShowScopesSim, FollowsInteractiveScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t.blk);\n"
      "    $showscopes;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastShownScope(), "t.blk");
}

}  // namespace
