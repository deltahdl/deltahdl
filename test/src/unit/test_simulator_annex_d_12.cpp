#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_annex_d_call_forms.h"

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

std::string FunctionDesignWith(const std::string& call) {
  std::string src =
      "module child;\n"
      "  function int fc; return 0; endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  function int ft; return 0; endfunction\n"
      "  initial begin : blk\n"
      "    ";
  src += call;
  src += "\n  end\nendmodule\n";
  return src;
}

TEST(OptionalShowScopesSim, FunctionsAreListedAtTheLevelAndBelow) {
  SimFixture level;
  EXPECT_EQ(RunCapture(FunctionDesignWith("$showscopes;"), level),
            "t.blk\nt.c1\nt.ft\n");
  SimFixture below;
  EXPECT_EQ(RunCapture(FunctionDesignWith("$showscopes(1);"), below),
            "t.blk\nt.c1\nt.c1.fc\nt.ft\n");
}

TEST(OptionalShowScopesSim, EveryNonzeroValueListsEveryScopeBelow) {
  for (const char* call :
       {"$showscopes(2);", "$showscopes(-1);", "$showscopes(3 - 2);"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(ListedDesignWith(call), f),
              "t.blk\nt.blk.inner\nt.c1\nt.c1.tk\nt.tt\n")
        << call;
  }
}

std::string ListedDesignWithVariable(const std::string& value) {
  std::string src = ListedDesignWith("$showscopes(m);");
  std::string decl = "  int m = ";
  decl += value;
  decl += ";\n";
  src.insert(src.find("  task tt;"), decl);
  return src;
}

TEST(OptionalShowScopesSim, AVariableArgumentDecidesByItsValue) {
  SimFixture nonzero;
  EXPECT_EQ(RunCapture(ListedDesignWithVariable("1"), nonzero),
            "t.blk\nt.blk.inner\nt.c1\nt.c1.tk\nt.tt\n");
  SimFixture zero;
  EXPECT_EQ(RunCapture(ListedDesignWithVariable("0"), zero),
            "t.blk\nt.c1\nt.tt\n");
}

constexpr const char* kShowScopesForm =
    "$showscopes is written as a task statement with no argument list or with "
    "one integer argument, and this call is not";

TEST(OptionalShowScopesForm, DISABLED_TwoArgumentsAreReported) {
  ExpectOnlyTheMalformedCallReported("$showscopes(1)", "$showscopes(1, 2)",
                                     kShowScopesForm, "D.12");
}

TEST(OptionalShowScopesForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$showscopes", "$showscopes()",
                                     kShowScopesForm, "D.12");
}

}  // namespace
