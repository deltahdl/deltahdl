#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(HierarchicalNameFormat, TopLevelModuleName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial $display(\"%m\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip\n");
}

TEST(HierarchicalNameFormat, PercentMConsumesNoArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    $display(\"%m=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip=42\n");
}

TEST(HierarchicalNameFormat, NestedNamedBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      $display(\"%m\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.outer.inner\n");
}

TEST(HierarchicalNameFormat, SubroutineScopeInHierarchy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  task show;\n"
      "    $display(\"%m\");\n"
      "  endtask\n"
      "  initial show;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.show\n");
}

TEST(HierarchicalNameFormat, ChildInstancePathReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  initial $display(\"%m\");\n"
      "endmodule\n"
      "module chip;\n"
      "  leaf u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.u1\n");
}

TEST(HierarchicalNameFormat, FunctionScopeInHierarchy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  function int get;\n"
      "    $display(\"%m\");\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial y = get();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.get\n");
}

TEST(HierarchicalNameFormat, FunctionNamedBlockInHierarchy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  function void f;\n"
      "    begin : b\n"
      "      $display(\"%m\");\n"
      "    end\n"
      "  endfunction\n"
      "  initial f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.f.b\n");
}

TEST(HierarchicalNameFormat, LabeledStatementScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial lbl: $display(\"%m\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.lbl\n");
}

TEST(HierarchicalNameFormat, LabeledLoopEnclosesCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial begin\n"
      "    lp: repeat (1) $display(\"%m\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.lp\n");
}

TEST(HierarchicalNameFormat, UppercaseFormInWriteTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial $write(\"%M\\n\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip\n");
}

TEST(HierarchicalNameFormat, BinaryRadixTaskPositionUnaffected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial $displayb(\"%m\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip\n");
}

TEST(HierarchicalNameFormat, StrobedTaskPosition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial $strobe(\"%m\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip\n");
}

TEST(HierarchicalNameFormat, SubroutineWithinInstanceComposesPath) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  task show;\n"
      "    $display(\"%m\");\n"
      "  endtask\n"
      "  initial show;\n"
      "endmodule\n"
      "module chip;\n"
      "  leaf u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.u1.show\n");
}

TEST(HierarchicalNameFormat, InstanceInAGenerateBlockIsNamedThroughIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p(input var int v);\n"
                       "  initial #1 $display(\"%m\");\n"
                       "endprogram\n"
                       "module top;\n"
                       "  int arr[2];\n"
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "    p pi(arr[i]);\n"
                       "  end\n"
                       "  if (1) begin : c\n"
                       "    p mc(arr[0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "top.g[0].pi\ntop.g[1].pi\ntop.c.mc\n");
  SimFixture g;
  EXPECT_EQ(RunCapture("module leaf; initial $display(\"%m\"); endmodule\n"
                       "module mid;\n"
                       "  leaf l();\n"
                       "  for (genvar j = 0; j < 2; j++) begin : h\n"
                       "    leaf l2();\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  for (genvar i = 0; i < 1; i++) begin : g\n"
                       "    if (1) begin : c\n"
                       "      mid m();\n"
                       "    end\n"
                       "  end\n"
                       "endmodule\n",
                       g),
            "top.g[0].c.m.l\ntop.g[0].c.m.h[0].l2\ntop.g[0].c.m.h[1].l2\n");
}

TEST(HierarchicalNameFormat, ElementOfAnArrayOfInstancesIsNamedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf; initial $display(\"%m\"); endmodule\n"
                       "module top;\n"
                       "  leaf u[1:0]();\n"
                       "endmodule\n",
                       f),
            "top.u[0]\ntop.u[1]\n");
}

TEST(HierarchicalNameFormat, StaticInitializerNamesItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  string s = $sformatf(\"%m\");\n"
                       "  initial #1 $display(\"%s\", s);\n"
                       "endmodule\n"
                       "module mid;\n"
                       "  leaf u2();\n"
                       "endmodule\n"
                       "module top;\n"
                       "  mid u1();\n"
                       "endmodule\n",
                       f),
            "top.u1.u2\n");
}

TEST(HierarchicalNameFormat,
     DISABLED_AnUnnamedForkInsideANamedBlockNamesTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial begin : b\n"
                       "    fork\n"
                       "      $display(\"%m\");\n"
                       "    join\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.b\n");
}

TEST(HierarchicalNameFormat, DISABLED_ANamedForkWithJoinNamesTheFork) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial begin\n"
                       "    fork : f\n"
                       "      $display(\"%m\");\n"
                       "    join\n"
                       "    #1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.f\n");
}

TEST(HierarchicalNameFormat, DISABLED_ANamedForkWithJoinAnyNamesTheFork) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial begin\n"
                       "    fork : f\n"
                       "      $display(\"%m\");\n"
                       "    join_any\n"
                       "    #1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.f\n");
}

TEST(HierarchicalNameFormat, DISABLED_ANamedForkWithJoinNoneNamesTheFork) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial begin\n"
                       "    fork : f\n"
                       "      $display(\"%m\");\n"
                       "    join_none\n"
                       "    #1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.f\n");
}

TEST(HierarchicalNameFormat, DISABLED_ANamedBlockInsideANamedForkNamesBoth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial fork : f\n"
                       "    begin : b\n"
                       "      $display(\"%m\");\n"
                       "    end\n"
                       "  join\n"
                       "endmodule\n",
                       f),
            "chip.f.b\n");
}

TEST(HierarchicalNameFormat, DISABLED_AnUnnamedForkInsideATaskNamesTheTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  task tk;\n"
                       "    fork\n"
                       "      $display(\"%m\");\n"
                       "    join\n"
                       "  endtask\n"
                       "  initial tk;\n"
                       "endmodule\n",
                       f),
            "chip.tk\n");
}

TEST(HierarchicalNameFormat,
     DISABLED_AForkJoinNoneInsideAFunctionNamesTheFunction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  function void fn();\n"
                       "    fork\n"
                       "      $display(\"%m\");\n"
                       "    join_none\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    fn();\n"
                       "    #1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.fn\n");
}

TEST(HierarchicalNameFormat, AForkInAProcedureOfAModuleNamesTheEnclosingScope) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  logic go = 0;\n"
                       "  always @(go) fork\n"
                       "    $display(\"%m\");\n"
                       "  join\n"
                       "  initial #1 go = 1;\n"
                       "endmodule\n",
                       f),
            "chip\n");
}

TEST(HierarchicalNameFormat,
     AForkInAProcedureOfAnInterfaceNamesTheEnclosingScope) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  logic go = 0;\n"
                       "  always @(go) fork\n"
                       "    $display(\"%m\");\n"
                       "  join\n"
                       "  initial #1 go = 1;\n"
                       "endinterface\n"
                       "module chip;\n"
                       "  ifc u();\n"
                       "endmodule\n",
                       f),
            "chip.u\n");
}

TEST(HierarchicalNameFormat,
     AForkInAProcedureOfAProgramNamesTheEnclosingScope) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program prg;\n"
                       "  initial fork\n"
                       "    $display(\"%m\");\n"
                       "  join\n"
                       "endprogram\n"
                       "module chip;\n"
                       "  prg u();\n"
                       "endmodule\n",
                       f),
            "chip.u\n");
}

TEST(HierarchicalNameFormat,
     AForkInAProcedureOfAGenerateBlockNamesTheEnclosingScope) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  if (1) begin : g\n"
                       "    logic go = 0;\n"
                       "    always @(go) fork\n"
                       "      $display(\"%m\");\n"
                       "    join\n"
                       "    initial #1 go = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.g\n");
}

TEST(HierarchicalNameFormat, ALabelledImmediateAssertionInAForkNamesTheLabel) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial fork\n"
                       "    a1: assert (1) $display(\"%m\");\n"
                       "  join\n"
                       "endmodule\n",
                       f),
            "chip.a1\n");
}

TEST(HierarchicalNameFormat, TheSameStatementsInABeginEndNameTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module chip;\n"
                       "  initial begin : b\n"
                       "    begin\n"
                       "      $display(\"%m\");\n"
                       "    end\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "chip.b\n");
}

TEST(HierarchicalNameFormat,
     DISABLED_APackageFunctionNamesThePackageAndTheFunction) {
  SimFixture f;
  std::string out = RunCapture(
      "package pkg;\n"
      "  function void pf();\n"
      "    $display(\"%m\");\n"
      "  endfunction\n"
      "endpackage\n"
      "module chip;\n"
      "  initial pkg::pf();\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("pkg"), std::string::npos) << out;
  EXPECT_NE(out.find("pf"), std::string::npos) << out;
}

TEST(HierarchicalNameFormat, DISABLED_AClassMethodNamesTheClassAndTheMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "module chip;\n"
      "  class C;\n"
      "    static function void cm();\n"
      "      $display(\"%m\");\n"
      "    endfunction\n"
      "  endclass\n"
      "  initial C::cm();\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find('C'), std::string::npos) << out;
  EXPECT_NE(out.find("cm"), std::string::npos) << out;
}

}  // namespace
