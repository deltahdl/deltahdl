#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_annex_d_call_forms.h"
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

std::string ListedScopeWithoutAReport(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  EXPECT_FALSE(f.has_errors) << src;
  return f.ctx.LastListedScope();
}

TEST(OptionalListSim, ArgumentListsAnInstance) {
  EXPECT_EQ(ListedScopeWithoutAReport("module leaf;\n"
                                      "endmodule\n"
                                      "module t;\n"
                                      "  leaf u1();\n"
                                      "  initial $list(t.u1);\n"
                                      "endmodule\n"),
            "t.u1");
}

TEST(OptionalListSim, ArgumentListsATask) {
  EXPECT_EQ(ListedScopeWithoutAReport("module leaf;\n"
                                      "  task tk; endtask\n"
                                      "endmodule\n"
                                      "module t;\n"
                                      "  leaf u1();\n"
                                      "  initial $list(t.u1.tk);\n"
                                      "endmodule\n"),
            "t.u1.tk");
}

TEST(OptionalListSim, BothFormsListWithoutAReportWhereverTheyRun) {
  struct Placement {
    const char* src;
    const char* listed;
  };
  const Placement kPlacements[] = {
      {"module t;\n"
       "  task tk; $list; endtask\n"
       "  initial tk();\n"
       "endmodule\n",
       "t"},
      {"module t;\n"
       "  initial begin : blk\n"
       "    tk();\n"
       "  end\n"
       "  task tk; $list(t.blk); endtask\n"
       "endmodule\n",
       "t.blk"},
      {"module t;\n"
       "  function void fn; $list; endfunction\n"
       "  initial fn();\n"
       "endmodule\n",
       "t"},
      {"module t;\n"
       "  initial begin : blk\n"
       "    fn();\n"
       "  end\n"
       "  function void fn; $list(t.blk); endfunction\n"
       "endmodule\n",
       "t.blk"},
      {"module t;\n"
       "  class C;\n"
       "    function void m; $list; endfunction\n"
       "  endclass\n"
       "  initial begin\n"
       "    C c;\n"
       "    c = new;\n"
       "    c.m();\n"
       "  end\n"
       "endmodule\n",
       "t"},
      {"module t;\n"
       "  class C;\n"
       "    function void m; $list(t.blk); endfunction\n"
       "  endclass\n"
       "  initial begin : blk\n"
       "    C c;\n"
       "    c = new;\n"
       "    c.m();\n"
       "  end\n"
       "endmodule\n",
       "t.blk"},
      {"program p;\n"
       "  initial $list;\n"
       "endprogram\n",
       "p"},
      {"program p;\n"
       "  initial begin : blk\n"
       "    $list(p.blk);\n"
       "  end\n"
       "endprogram\n",
       "p.blk"},
  };
  for (const Placement& placement : kPlacements) {
    EXPECT_EQ(ListedScopeWithoutAReport(placement.src), placement.listed)
        << placement.src;
  }
}

TEST(OptionalListSim, DISABLED_RelativeNamesListTheObjectTheyResolveTo) {
  EXPECT_EQ(ListedScopeWithoutAReport("module t;\n"
                                      "  initial begin : blk\n"
                                      "    $list(blk);\n"
                                      "  end\n"
                                      "endmodule\n"),
            "t.blk");
  constexpr const char* kLeaf =
      "module leaf;\n"
      "  initial begin : b\n"
      "  end\n"
      "endmodule\n";
  std::string down = kLeaf;
  down +=
      "module t;\n"
      "  leaf u();\n"
      "  initial $list(u);\n"
      "endmodule\n";
  EXPECT_EQ(ListedScopeWithoutAReport(down), "t.u");
  std::string down_block = kLeaf;
  down_block +=
      "module t;\n"
      "  leaf u();\n"
      "  initial $list(u.b);\n"
      "endmodule\n";
  EXPECT_EQ(ListedScopeWithoutAReport(down_block), "t.u.b");
}

TEST(OptionalListSim, AParameterOrAPackageNameIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "endpackage\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "  initial begin\n"
      "    $list(t);\n"
      "    $list(t.P);\n"
      "    $list(pk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$list takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.P' is none",
                            7, "D.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$list takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'pk' is none",
                            8, "D.6"));
  EXPECT_EQ(f.ctx.LastListedScope(), "t");
}

TEST(OptionalListSim, DISABLED_TheListingIsWrittenToTheOutput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module listed_top;\n"
      "  initial begin : inner_blk\n"
      "    $list;\n"
      "    $scope(listed_top.inner_blk);\n"
      "    $list;\n"
      "  end\n"
      "endmodule\n",
      f);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  std::string out = testing::internal::GetCapturedStdout();
  auto top = out.find("listed_top");
  ASSERT_NE(top, std::string::npos) << out;
  EXPECT_NE(out.find("listed_top.inner_blk", top), std::string::npos) << out;
}

constexpr const char* kListForm =
    "$list is written as a task statement with no argument or with one "
    "hierarchical name, and this call is not";

TEST(OptionalListForm, DISABLED_TwoArgumentsAreReported) {
  ExpectOnlyTheMalformedCallReported("$list(t)", "$list(t, t)", kListForm,
                                     "D.6");
}

TEST(OptionalListForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$list", "$list()", kListForm, "D.6");
}

TEST(OptionalListForm, DISABLED_AnArgumentThatIsNoNameIsReported) {
  ExpectOnlyTheMalformedCallReported("$list(t)", "$list(1 + 2)", kListForm,
                                     "D.6");
  ExpectOnlyTheMalformedCallReported("$list(t)", "$list(\"t\")", kListForm,
                                     "D.6");
}

TEST(OptionalListForm, DISABLED_UseAsAFunctionIsReported) {
  ExpectOnlyTheMalformedCallReported("$list", "v = $list", kListForm, "D.6");
}

}  // namespace
