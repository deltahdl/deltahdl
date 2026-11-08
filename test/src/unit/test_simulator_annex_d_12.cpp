#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(OptionalShowScopesSim, ListsTheScopesAtTheCurrentLevel) {
  SimFixture f;
  std::string out = RunCapture(ListedDesignWith("$showscopes;"), f);
  EXPECT_EQ(out, "t.blk\nt.c1\nt.tt\n");
}

TEST(OptionalShowScopesSim, ANonzeroArgumentListsEveryScopeBelow) {
  SimFixture f;
  std::string out = RunCapture(ListedDesignWith("$showscopes(1);"), f);
  EXPECT_EQ(out, "t.blk\nt.blk.inner\nt.c1\nt.c1.tk\nt.tt\n");
}

TEST(OptionalShowScopesSim, AZeroArgumentListsTheCurrentLevelAlone) {
  SimFixture f;
  std::string out = RunCapture(ListedDesignWith("$showscopes(0);"), f);
  EXPECT_EQ(out, "t.blk\nt.c1\nt.tt\n");
}

TEST(OptionalShowScopesSim, ListsTheLevelOfTheScopeSetByScope) {
  SimFixture f;
  std::string out =
      RunCapture(ListedDesignWith("$scope(t.c1); $showscopes;"), f);
  EXPECT_EQ(out, "t.c1.tk\n");
}

TEST(OptionalShowScopesSim, AScopeDefiningNothingListsNothing) {
  SimFixture f;
  std::string out =
      RunCapture(ListedDesignWith("$scope(t.blk.inner); $showscopes(1);"), f);
  EXPECT_EQ(out, "");
}

}  // namespace
