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

}  // namespace
