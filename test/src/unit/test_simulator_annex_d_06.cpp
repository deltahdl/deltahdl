#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(OptionalListSim, AnArgumentNamingNoScopeIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin : blk\n"
      "    $list(t.blk);\n"
      "    $list(t.nope);\n"
      "    $list(t.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$list takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.nope' is none",
                            5, "D.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$list takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.v' is none",
                            6, "D.6"));
  EXPECT_EQ(f.ctx.LastListedScope(), "t.blk");
}

TEST(OptionalListSim, ArgumentAcceptsAnInstanceATaskAndAFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  task tk; endtask\n"
      "  function int fn; return 1; endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u1();\n"
      "  initial begin\n"
      "    $list(t.u1);\n"
      "    $list(t.u1.tk);\n"
      "    $list(t.u1.fn);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.ctx.LastListedScope(), "t.u1.fn");
}

}  // namespace
