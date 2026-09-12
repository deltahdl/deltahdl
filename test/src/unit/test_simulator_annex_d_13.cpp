#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Annex D.13: invoked without arguments, $showvars reports the status of all
// variables in the current scope. The scope it operates on is the current
// interactive scope, which starts as the first top-level module.
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

// Annex D.13: with no argument every variable in the current scope is reported,
// so no specific variable names are singled out.
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

// Annex D.13: invoked with a list of variables, $showvars reports only the
// status of the specified variables.
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

// Annex D.13: when the list includes a bit-select of a vector, the status of
// all bits of that vector is displayed, so the selection is reported by the
// name of its underlying vector.
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

// Annex D.13: a part-select of a vector is likewise reported by the name of the
// whole vector, since all of its bits are displayed.
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

// Annex D.13: $showvars operates on the current scope, so retargeting the
// interactive scope with $scope (Annex D.11) changes which scope its report
// applies to.
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

// Annex D.13: a list may mix a plain variable with a selection of a vector. The
// plain variable is reported by its own name while the selection is reported by
// the name of the whole vector, so a single call records both forms.
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

// Annex D.13: when several selections of different vectors appear in the list,
// each selection collapses independently to the name of its own vector.
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

// Annex D.13: an indexed part-select (+:) of a vector likewise displays all
// bits of the vector, so it too is reported by the name of the whole vector.
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

// The design the status tests share: the top declares a net no one drives, a
// reg no one assigns and a vector with an initial value, and holds an instance
// declaring a vector of its own, so the status printed tells a z, an x, a
// value, and which scope's variables were reported.
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

// Annex D.13: with no argument the status of every reg and net variable of
// the current scope is displayed, here each by its name and its value in
// binary, nets before regs in declaration order: the undriven net is z, the
// unassigned reg x, and the vector shows every bit.
TEST(OptionalShowVarsSim, NoArgumentDisplaysEveryVariableOfTheScope) {
  SimFixture f;
  std::string out = RunCapture(StatusDesignWith("$showvars;"), f);
  EXPECT_EQ(out, "w = z\na = x\nv = 01011010\n");
}

// Annex D.13: with a list of variables only the named ones are displayed, in
// the order given.
TEST(OptionalShowVarsSim, AListDisplaysTheNamedVariablesAlone) {
  SimFixture f;
  std::string out = RunCapture(StatusDesignWith("$showvars(v, w);"), f);
  EXPECT_EQ(out, "v = 01011010\nw = z\n");
}

// Annex D.13: a bit-select or part-select of a vector in the list displays
// the status of all the bits of that vector, so the selected bit's own value
// of 0 is not what is printed.
TEST(OptionalShowVarsSim, ASelectOfAVectorDisplaysAllItsBits) {
  SimFixture f;
  std::string out = RunCapture(StatusDesignWith("$showvars(v[0], v[7:4]);"), f);
  EXPECT_EQ(out, "v = 01011010\nv = 01011010\n");
}

// Annex D.13: the variables displayed are the current scope's, so after
// $scope moves the interactive scope into the instance the instance's vector
// is displayed and the top's three are not, whether every variable is asked
// for or the instance's is named.
TEST(OptionalShowVarsSim, TheScopeSetByScopeSelectsWhoseVariablesAreShown) {
  SimFixture f;
  std::string out =
      RunCapture(StatusDesignWith("$scope(t.c1); $showvars; $showvars(q);"), f);
  EXPECT_EQ(out, "q = 1010\nq = 1010\n");
}

// Annex D.13: a name the scope declares no variable under is displayed as
// having none rather than as some other scope's variable of that name: the
// instance declares no v, so the top's v is not what a $showvars(v) in the
// instance's scope shows.
TEST(OptionalShowVarsSim, ANameTheScopeDoesNotDeclareHasNoStatus) {
  SimFixture f;
  std::string out =
      RunCapture(StatusDesignWith("$scope(t.c1); $showvars(v);"), f);
  EXPECT_EQ(out, "v = <no such variable>\n");
}

// Annex D.13: a named block declares no reg or net variable of the design, so
// with the interactive scope set to one and no argument nothing is displayed,
// and a name given is looked up from where the call stands.
TEST(OptionalShowVarsSim, ANamedBlockScopeShowsWhatItIsAsked) {
  SimFixture f;
  std::string out = RunCapture(
      StatusDesignWith("$scope(t.blk); $showvars; $showvars(a);"), f);
  EXPECT_EQ(out, "a = x\n");
}

}  // namespace
