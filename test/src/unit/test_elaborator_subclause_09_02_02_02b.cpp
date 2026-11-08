#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

void ExpectFunctionTargetDrivenTwice(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  logic a, y, z, ok;\n"
      "  logic [3:0] w;\n"
      "  int arr[4];\n"
      "  int q[$];\n"
      "  function automatic logic f();\n"
      "    y = a;\n"
      "    return a;\n"
      "  endfunction\n"
      "  always_comb\n"
      "    " +
      stmt +
      "\n"
      "  initial y = a;\n"
      "endmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "variable 'y' driven by always_comb and another process",
                    LineHolding(src, "always_comb"), "9.2.2.2"));
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssertionPassStmtIsADriver) {
  ExpectFunctionTargetDrivenTwice("assert (ok) z = f();");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssertionFailStmtIsADriver) {
  ExpectFunctionTargetDrivenTwice("assert (ok) else z = f();");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromARandcaseItemIsADriver) {
  ExpectFunctionTargetDrivenTwice("randcase 1: z = f(); endcase");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromARandsequenceCodeBlockIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { z = f(); };\n"
      "      endsequence\n"
      "    end");
}

TEST(AlwaysCombMultiDriver,
     FunctionCalledFromARandsequenceWeightCodeBlockIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { z = f(); };\n"
      "        alt : { z = a; };\n"
      "      endsequence\n"
      "    end");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromABlockVarInitializerIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      int r = f();\n"
      "      z = a;\n"
      "    end");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssignmentTargetIsADriver) {
  ExpectFunctionTargetDrivenTwice("w[f()] = a;");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnIntraAssignmentDelayIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= #(f()) a;");
}

TEST(AlwaysCombMultiDriver,
     FunctionCalledFromAnIntraAssignmentCycleDelayIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= ##(f()) a;");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnEventExpressionIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= @(f()) a;");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnEventIffConditionIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= @(posedge a iff f()) 1'b1;");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromARepeatEventCountIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= repeat (f()) @(posedge a) 1'b1;");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssertedExpressionIsADriver) {
  ExpectFunctionTargetDrivenTwice("assert (f());");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromACaseItemPatternIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "case (a)\n"
      "      f(): z = 1'b1;\n"
      "      default: z = 1'b0;\n"
      "    endcase");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromARandcaseWeightIsADriver) {
  ExpectFunctionTargetDrivenTwice("randcase f(): z = a; endcase");
}

TEST(AlwaysCombMultiDriver,
     FunctionCalledFromABlockUnpackedDimensionIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      int u[f()];\n"
      "      z = a;\n"
      "    end");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAPartSelectUpperBoundIsADriver) {
  ExpectFunctionTargetDrivenTwice("z = w[3:f()];");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAWithClauseIsADriver) {
  ExpectFunctionTargetDrivenTwice("z = q.sum() with (f());");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAReplicationCountIsADriver) {
  ExpectFunctionTargetDrivenTwice("z = {f(){1'b0}};");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssignmentPatternKeyIsADriver) {
  ExpectFunctionTargetDrivenTwice("arr = '{f(): 1};");
}

TEST(AlwaysCombLatchWarning, AssertionPassStatementAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

TEST(AlwaysCombLatchWarning, AssertionFailStatementAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) else y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

TEST(AlwaysCombLatchWarning, AssertionBothActionArmsStillInferLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) y = a; else y = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

TEST(AlwaysCombLatchWarning, RandcaseItemAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb randcase 1: y = a; endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

TEST(AlwaysCombLatchWarning, RandsequenceCodeBlockAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb\n"
      "    randsequence(main)\n"
      "      main : { y = a; };\n"
      "    endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

TEST(AlwaysCombLatchWarning, ForkJoinNoneArmAssignmentInfersLatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb fork y = a; join_none\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

TEST(AlwaysCombLatchWarning, ForInitializationAssignmentIsCombinational) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, y;\n"
      "  int i;\n"
      "  always_comb begin\n"
      "    for (y = 1'b0; i < 2; i++)\n"
      "      if (sel) y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysCombLatchWarning, ForStepAssignmentIsCombinational) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, y;\n"
      "  int i;\n"
      "  always_comb begin\n"
      "    for ( ; i < 2; i++, y = a)\n"
      "      if (sel) y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysCombMultiDriver, ForHeaderVariablesOfTwoProceduresAreNotShared) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a[3], not_a[3], b[3], z[3];\n"
      "  always_comb begin\n"
      "    for (int j = 0; j < 3; j++) not_a[j] = !a[j];\n"
      "  end\n"
      "  always_comb begin : a1\n"
      "    for (int j = 0; j < 3; j++) z[j] = a[j] | b[j];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver, BlockVariablesOfThreeProceduresAreNotShared) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y, z;\n"
      "  always_comb begin\n"
      "    logic tmp;\n"
      "    tmp = !a; y = tmp;\n"
      "  end\n"
      "  always_comb begin\n"
      "    logic tmp;\n"
      "    tmp = a | b; z = tmp;\n"
      "  end\n"
      "  initial begin\n"
      "    logic tmp;\n"
      "    tmp = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombMultiDriver,
     ModuleVariableAssignedAfterAForHeaderLocalIsShared) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y[2];\n"
      "  int j;\n"
      "  always_comb begin\n"
      "    for (int j = 0; j < 2; j++) y[j] = a;\n"
      "    j = 0;\n"
      "  end\n"
      "  always_comb j = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'j' driven by multiple", 8, "9.2.2.2"));
}

TEST(AlwaysCombMultiDriver, ModuleVariableAssignedOutsideABlockLocalIsShared) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb begin\n"
      "    begin\n"
      "      logic y;\n"
      "      y = a;\n"
      "    end\n"
      "    y = b;\n"
      "  end\n"
      "  always_comb y = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'y' driven by multiple", 10, "9.2.2.2"));
}

TEST(AlwaysCombMultiDriver, CalledFunctionsOwnNamesAreNoDrivers) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic a, b, y, z;\n"
      "  function automatic logic inv(logic x);\n"
      "    logic t; t = !x; x = t; inv = t;\n"
      "  endfunction\n"
      "  always_comb y = inv(a);\n"
      "  always_comb z = inv(b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "driven by multiple", 6, "9.2.2.2"));
}

TEST(AlwaysCombMultiDriver, AWriteThroughAnotherProcessesFunctionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic a, y;\n"
      "  function void set_y(); y = 1; endfunction\n"
      "  always_comb y = a;\n"
      "  initial set_y();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'y' driven by always_comb and another "
                            "process",
                            3, "9.2.2.2"));
}

}  // namespace
