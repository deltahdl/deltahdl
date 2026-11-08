#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(OptionalShowVarsSim, NoArgumentUsesCurrentScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    $showvars;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastShowVarsScope(), "t");
}

TEST(OptionalShowVarsSim, NoArgumentNamesNoSpecificVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    $showvars;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.ShowVarsVariables().empty());
}

TEST(OptionalShowVarsSim, ListRecordsSpecifiedVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    $showvars(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  ASSERT_EQ(f.ctx.ShowVarsVariables().size(), 2u);
  EXPECT_EQ(f.ctx.ShowVarsVariables()[0], "a");
  EXPECT_EQ(f.ctx.ShowVarsVariables()[1], "b");
}

TEST(OptionalShowVarsSim, BitSelectReportsWholeVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg [7:0] v;\n"
      "  initial begin\n"
      "    $showvars(v[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  ASSERT_EQ(f.ctx.ShowVarsVariables().size(), 1u);
  EXPECT_EQ(f.ctx.ShowVarsVariables()[0], "v");
}

TEST(OptionalShowVarsSim, PartSelectReportsWholeVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg [7:0] v;\n"
      "  initial begin\n"
      "    $showvars(v[5:2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  ASSERT_EQ(f.ctx.ShowVarsVariables().size(), 1u);
  EXPECT_EQ(f.ctx.ShowVarsVariables()[0], "v");
}

TEST(OptionalShowVarsSim, FollowsInteractiveScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t.blk);\n"
      "    $showvars;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastShowVarsScope(), "t.blk");
}

TEST(OptionalShowVarsSim, MixedPlainAndSelectList) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg a;\n"
      "  reg [7:0] v;\n"
      "  initial begin\n"
      "    $showvars(a, v[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  ASSERT_EQ(f.ctx.ShowVarsVariables().size(), 2u);
  EXPECT_EQ(f.ctx.ShowVarsVariables()[0], "a");
  EXPECT_EQ(f.ctx.ShowVarsVariables()[1], "v");
}

TEST(OptionalShowVarsSim, MultipleSelectsCollapseEach) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg [7:0] v;\n"
      "  reg [7:0] w;\n"
      "  initial begin\n"
      "    $showvars(v[3], w[5:2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  ASSERT_EQ(f.ctx.ShowVarsVariables().size(), 2u);
  EXPECT_EQ(f.ctx.ShowVarsVariables()[0], "v");
  EXPECT_EQ(f.ctx.ShowVarsVariables()[1], "w");
}

TEST(OptionalShowVarsSim, IndexedPartSelectReportsWholeVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg [7:0] v;\n"
      "  initial begin\n"
      "    $showvars(v[2+:3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  ASSERT_EQ(f.ctx.ShowVarsVariables().size(), 1u);
  EXPECT_EQ(f.ctx.ShowVarsVariables()[0], "v");
}

constexpr const char* kStatusDesign =
    "module child;\n"
    "  reg [3:0] q = 4'b1010;\n"
    "endmodule\n"
    "module t;\n"
    "  wire w;\n"
    "  reg a;\n"
    "  reg [7:0] v = 8'h5a;\n"
    "  child c1();\n"
    "  initial begin : blk\n"
    "    #1 %s\n"
    "  end\n"
    "endmodule\n";

std::string StatusDesignWith(const std::string& calls) {
  std::string src = kStatusDesign;
  src.replace(src.find("%s"), 2, calls);
  return src;
}

TEST(OptionalShowVarsSim, NoArgumentDisplaysEveryVariableOfTheScope) {
  SimFixture f;
  std::string out = RunCapture(StatusDesignWith("$showvars;"), f);
  EXPECT_EQ(out, "w = z\na = x\nv = 01011010\n");
}

TEST(OptionalShowVarsSim, AListDisplaysTheNamedVariablesAlone) {
  SimFixture f;
  std::string out = RunCapture(StatusDesignWith("$showvars(v, w);"), f);
  EXPECT_EQ(out, "v = 01011010\nw = z\n");
}

TEST(OptionalShowVarsSim, ASelectOfAVectorDisplaysAllItsBits) {
  SimFixture f;
  std::string out = RunCapture(StatusDesignWith("$showvars(v[0], v[7:4]);"), f);
  EXPECT_EQ(out, "v = 01011010\nv = 01011010\n");
}

TEST(OptionalShowVarsSim, TheScopeSetByScopeSelectsWhoseVariablesAreShown) {
  SimFixture f;
  std::string out =
      RunCapture(StatusDesignWith("$scope(t.c1); $showvars; $showvars(q);"), f);
  EXPECT_EQ(out, "q = 1010\nq = 1010\n");
}

TEST(OptionalShowVarsSim, ANameTheScopeDoesNotDeclareHasNoStatus) {
  SimFixture f;
  std::string out =
      RunCapture(StatusDesignWith("$scope(t.c1); $showvars(v);"), f);
  EXPECT_EQ(out, "v = <no such variable>\n");
}

TEST(OptionalShowVarsSim, ANamedBlockScopeShowsWhatItIsAsked) {
  SimFixture f;
  std::string out = RunCapture(
      StatusDesignWith("$scope(t.blk); $showvars; $showvars(a);"), f);
  EXPECT_EQ(out, "a = x\n");
}

}  // namespace
