#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_annex_d_call_forms.h"

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

std::string NetDesignWith(const std::string& calls) {
  std::string src =
      "module t;\n"
      "  wire [3:0] n = 4'b1100;\n"
      "  reg a;\n"
      "  reg [7:0] v = 8'h5a;\n"
      "  initial begin\n"
      "    #1 ";
  src += calls;
  src += "\n  end\nendmodule\n";
  return src;
}

TEST(OptionalShowVarsSim, AVectorNetDisplaysEveryBit) {
  SimFixture all;
  EXPECT_EQ(RunCapture(NetDesignWith("$showvars;"), all),
            "n = 1100\na = x\nv = 01011010\n");
  SimFixture listed;
  EXPECT_EQ(RunCapture(NetDesignWith("$showvars(n);"), listed), "n = 1100\n");
}

TEST(OptionalShowVarsSim, EverySelectFormDisplaysTheWholeVector) {
  struct SelectCase {
    const char* call;
    const char* shown;
  };
  const SelectCase kCases[] = {
      {"$showvars(v[2+:3]);", "v = 01011010\n"},
      {"$showvars(v[7-:2]);", "v = 01011010\n"},
      {"$showvars(n[1]);", "n = 1100\n"},
      {"$showvars(n[2:1]);", "n = 1100\n"},
      {"$showvars(a, v[3], n[2:1]);", "a = x\nv = 01011010\nn = 1100\n"},
  };
  for (const auto& c : kCases) {
    SimFixture f;
    EXPECT_EQ(RunCapture(NetDesignWith(c.call), f), c.shown) << c.call;
  }
}

TEST(OptionalShowVarsSim, ACallInAProgramTaskShowsTheProgramVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "program p;\n"
      "  reg [2:0] r = 3'b101;\n"
      "  task show;\n"
      "    $showvars(r);\n"
      "  endtask\n"
      "  initial show();\n"
      "endprogram\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "r = 101\n");
}

TEST(OptionalShowVarsSim, DISABLED_ANamedBlockScopeShowsItsOwnVariables) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg a;\n"
      "  initial begin : blk\n"
      "    reg [1:0] lr;\n"
      "    lr = 2'b10;\n"
      "    $scope(t.blk);\n"
      "    $showvars;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "lr = 10\n");
}

TEST(OptionalShowVarsSim, DISABLED_ATaskScopeShowsItsOwnVariables) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg a;\n"
      "  task tk;\n"
      "    reg [2:0] tr;\n"
      "    tr = 3'b110;\n"
      "    $scope(t.tk);\n"
      "    $showvars;\n"
      "  endtask\n"
      "  initial tk();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "tr = 110\n");
}

constexpr const char* kShowVarsForm =
    "$showvars is written as a task statement with no argument list or with a "
    "list of variables, and this call is not";

TEST(OptionalShowVarsForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$showvars", "$showvars()", kShowVarsForm,
                                     "D.13");
}

TEST(OptionalShowVarsForm, DISABLED_AnEntryThatIsNoVariableIsReported) {
  ExpectOnlyTheMalformedCallReported("$showvars(v, v[0])", "$showvars(v + 1)",
                                     kShowVarsForm, "D.13");
}

}  // namespace
