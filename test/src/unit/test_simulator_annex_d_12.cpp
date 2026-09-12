#include <string>

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

// The design the listing tests share: the top holds an instance, a task and a
// named block, the instance a task of its own and the block a block of its
// own, so the current level and the levels below it hold different names.
constexpr const char* kListedDesign =
    "module child;\n"
    "  task tk; endtask\n"
    "endmodule\n"
    "module t;\n"
    "  child c1();\n"
    "  task tt; endtask\n"
    "  initial begin : blk\n"
    "    begin : inner end\n"
    "    %s\n"
    "  end\n"
    "endmodule\n";

std::string ListedDesignWith(const std::string& calls) {
  std::string src = kListedDesign;
  src.replace(src.find("%s"), 2, calls);
  return src;
}

// Annex D.12: the list produced is of the modules, tasks, functions, and named
// blocks defined at the current scope level, so with no argument the top's
// instance, task and named block are printed, one complete name per line in
// sorted order, and the task the instance holds and the block the block holds
// are not.
TEST(OptionalShowScopesSim, ListsTheScopesAtTheCurrentLevel) {
  SimFixture f;
  std::string out = RunCapture(ListedDesignWith("$showscopes;"), f);
  EXPECT_EQ(out, "t.blk\nt.c1\nt.tt\n");
}

// Annex D.12: a nonzero argument lists every such object in or below the
// current scope, so the instance's task and the block's inner block join the
// list, each under the complete name of what holds it.
TEST(OptionalShowScopesSim, ANonzeroArgumentListsEveryScopeBelow) {
  SimFixture f;
  std::string out = RunCapture(ListedDesignWith("$showscopes(1);"), f);
  EXPECT_EQ(out, "t.blk\nt.blk.inner\nt.c1\nt.c1.tk\nt.tt\n");
}

// Annex D.12: a zero argument lists the current level alone, as no argument
// does, so the two print the same list.
TEST(OptionalShowScopesSim, AZeroArgumentListsTheCurrentLevelAlone) {
  SimFixture f;
  std::string out = RunCapture(ListedDesignWith("$showscopes(0);"), f);
  EXPECT_EQ(out, "t.blk\nt.c1\nt.tt\n");
}

// Annex D.12: the level listed is the current scope's, so after $scope moves
// the interactive scope into the instance the list is of what the instance
// defines, its task, and holds nothing of the top's.
TEST(OptionalShowScopesSim, ListsTheLevelOfTheScopeSetByScope) {
  SimFixture f;
  std::string out =
      RunCapture(ListedDesignWith("$scope(t.c1); $showscopes;"), f);
  EXPECT_EQ(out, "t.c1.tk\n");
}

// Annex D.12: a scope defining nothing below it, the inner block, lists
// nothing rather than itself.
TEST(OptionalShowScopesSim, AScopeDefiningNothingListsNothing) {
  SimFixture f;
  std::string out =
      RunCapture(ListedDesignWith("$scope(t.blk.inner); $showscopes(1);"), f);
  EXPECT_EQ(out, "");
}

}  // namespace
