#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(QualifiedIfSimulation, Unique0IfTakesCorrectBranch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    unique0 if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(QualifiedIfSimulation, UniqueIfNoMatchNoElseEmitsViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd7;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(QualifiedIfSimulation, PriorityIfNoMatchNoElseEmitsViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd9;\n"
      "    priority if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(QualifiedIfSimulation, UniqueIfWithExplicitElseSuppressesViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd7;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, Unique0IfNoMatchEmitsNoViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd9;\n"
      "    unique0 if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, UniqueIfOverlapEmitsViolationAndTakesFirst) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else if (1) x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(QualifiedIfSimulation, Unique0IfOverlapEmitsViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    unique0 if (1) x = 8'd10;\n"
                      "    else if (1) x = 8'd20;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(QualifiedIfSimulation, PriorityIfWithExplicitElseSuppressesViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd7;\n"
      "    priority if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, UniqueIfChainSingleMatchEmitsNoViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, PriorityIfOverlapDoesNotEmitViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else if (1) x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, UniqueIfOverlapWithElseStillEmitsViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(QualifiedIfSimulation,
     UniqueIfContinuesEvaluatingLaterConditionAfterMatch) {
  SimFixture f;
  auto [x, i] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  logic [7:0] x, i;\n"
                                 "  initial begin\n"
                                 "    i = 8'd0;\n"
                                 "    unique if (1) x = 8'd10;\n"
                                 "    else if (i++ == 8'd99) x = 8'd20;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "i");
  EXPECT_EQ(x, 10u);
  EXPECT_EQ(i, 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, QualifiedIfFallsToElse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (0) x = 8'd10;\n"
      "    else if (0) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(QualifiedIfSimulation, TheUniqueExampleReportsValuesNoConditionMatches) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic [2:0] a;\n"
                 "  initial\n"
                 "    for (int i = 0; i < 8; i++) begin\n"
                 "      a = i;\n"
                 "      unique if ((a==0) || (a==1)) $display(\"0 or 1\");\n"
                 "      else if (a == 2) $display(\"2\");\n"
                 "      else if (a == 4) $display(\"4\");\n"
                 "      #1;\n"
                 "    end\n"
                 "endmodule\n",
                 f),
      "0 or 1\n0 or 1\n2\n4\n");
  EXPECT_EQ(f.diag.WarningCount(), 4u);
}

TEST(QualifiedIfSimulation, ThePriorityExampleWithAnElseReportsNoValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [2:0] a;\n"
                       "  initial\n"
                       "    for (int i = 0; i < 8; i++) begin\n"
                       "      a = i;\n"
                       "      priority if (a[2:1]==0) $display(\"0 or 1\");\n"
                       "      else if (a[2] == 0) $display(\"2 or 3\");\n"
                       "      else $display(\"4 to 7\");\n"
                       "      #1;\n"
                       "    end\n"
                       "endmodule\n",
                       f),
            "0 or 1\n0 or 1\n2 or 3\n2 or 3\n4 to 7\n4 to 7\n4 to 7\n4 to 7\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation, TheUnique0ExampleReportsNoValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic [2:0] a;\n"
                 "  initial\n"
                 "    for (int i = 0; i < 8; i++) begin\n"
                 "      a = i;\n"
                 "      unique0 if ((a==0) || (a==1)) $display(\"0 or 1\");\n"
                 "      else    if (a == 2) $display(\"2\");\n"
                 "      else    if (a == 4) $display(\"4\");\n"
                 "      #1;\n"
                 "    end\n"
                 "endmodule\n",
                 f),
      "0 or 1\n0 or 1\n2\n4\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation,
     UniqueAndUnique0EvaluateTheConditionsAfterTheTrueOne) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a = 1, n = 0;\n"
                       "  function int f();\n"
                       "    n++;\n"
                       "    return 0;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    unique if (a == 1) $display(\"u first\");\n"
                       "    else if (f() == 1) $display(\"u second\");\n"
                       "    unique0 if (a == 1) $display(\"u0 first\");\n"
                       "    else if (a == 2) $display(\"u0 second\");\n"
                       "    else if (f() == 1) $display(\"u0 third\");\n"
                       "    #1 $display(\"%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "u first\nu0 first\n2\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(QualifiedIfSimulation,
     APriorityChainStopsEvaluatingAtTheFirstTrueCondition) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a = 1, n = 0;\n"
                       "  function int f();\n"
                       "    n++;\n"
                       "    return 1;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    priority if (a == 1) $display(\"first\");\n"
                       "    else if (f() == 1) $display(\"second\");\n"
                       "    priority if (a == 2) $display(\"first\");\n"
                       "    else if (f() == 1) $display(\"second\");\n"
                       "    #1 $display(\"%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "first\nsecond\n1\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
