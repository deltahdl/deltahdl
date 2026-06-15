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

}
