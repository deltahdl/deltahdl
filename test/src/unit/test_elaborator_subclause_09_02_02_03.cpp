#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AlwaysLatchElaboration, TimingControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch #5 if (en) q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, ForkJoinInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_latch shall not contain fork-join statements", 3, "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, IncompleteIfNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, CompleteIfElseWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch\n"
      "    if (en) q = a;\n"
      "    else q = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, CaseWithoutDefaultNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, CaseWithDefaultWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "      default: q = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, AlwaysLatchElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysLatch) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(AlwaysLatchElaboration, MultiDriverTwoAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch if (en) q = a;\n"
      "  always_latch if (en) q = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'q' driven by multiple", 4, "9.2.2.2"));
}

TEST(AlwaysLatchElaboration, AlwaysLatchInfersSensitivityFromBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

TEST(AlwaysLatchElaboration, EventControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q, clk;\n"
      "  always_latch @(posedge clk) if (en) q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_latch shall not have an explicit event control", 3, "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, UnconditionalAssignWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic d, q;\n"
      "  always_latch q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, IfElseIfElseChainWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, d1, d2, d3, q;\n"
      "  always_latch\n"
      "    if (a) q = d1;\n"
      "    else if (b) q = d2;\n"
      "    else q = d3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, TwoAlwaysLatchDifferentSignalsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q1, q2;\n"
      "  always_latch if (en) q1 = a;\n"
      "  always_latch if (en) q2 = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysLatchElaboration, ContinuousAssignAndAlwaysLatchSameVarErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  assign q = b;\n"
      "  always_latch if (en) q = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'q' driven by always_latch and continuous assignment", 4,
      "10.3.2"));
}

TEST(AlwaysLatchElaboration, WaitStatementInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    wait (en) q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, AlwaysLatchAndGeneralAlwaysSameVarErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch if (en) q = a;\n"
      "  always @(b) q = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'q' driven by always_latch and another process", 3, "9.2.2.2"));
}

TEST(AlwaysLatchElaboration, AlwaysLatchAndInitialSameVarErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, q;\n"
      "  initial q = 0;\n"
      "  always_latch if (en) q = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'q' driven by always_latch and another process", 4, "9.2.2.2"));
}

TEST(AlwaysLatchElaboration, AlwaysLatchAndGeneralAlwaysDifferentVarsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q1, q2;\n"
      "  always_latch if (en) q1 = a;\n"
      "  always @(b) q2 = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysLatchElaboration, BlockWrappingIncompleteIfNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, MultiDriverAlwaysLatchAndAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_comb q = a;\n"
      "  always_latch if (en) q = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'q' driven by multiple", 4, "9.2.2.2"));
}

TEST(AlwaysLatchElaboration, TwoAlwaysLatchIndependentArrayElementsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[0] = 8'd1;\n"
      "  always_latch if (en) arr[1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysLatchElaboration, TwoAlwaysLatchSameArrayElementErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[0] = 8'd1;\n"
      "  always_latch if (en) arr[0] = 8'd2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'arr[0]' driven by multiple", 5,
                            "9.2.2.2"));
}

TEST(AlwaysLatchElaboration,
     UnconditionalAssignBeforeIncompleteIfWarnsNoLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, e, q;\n"
      "  always_latch begin\n"
      "    q = d;\n"
      "    if (en) q = e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, CompleteIfElseLeavingOneOutputHeldNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, e, f2, q, r;\n"
      "  always_latch\n"
      "    if (en) begin\n"
      "      q = d;\n"
      "      r = e;\n"
      "    end else begin\n"
      "      q = f2;\n"
      "    end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, IndependentArrayElementsParamIndexNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int P0 = 0, parameter int P1 = 1);\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[P0] = 8'd1;\n"
      "  always_latch if (en) arr[P1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysLatchElaboration, OverlappingArrayElementsParamIndexErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter int P = 0);\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[P] = 8'd1;\n"
      "  always_latch if (en) arr[P] = 8'd2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'arr[0]' driven by multiple", 5,
                            "9.2.2.2"));
}

TEST(AlwaysLatchElaboration, IndependentArrayElementsLocalparamIndexNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P0 = 0;\n"
      "  localparam int P1 = 1;\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[P0] = 8'd1;\n"
      "  always_latch if (en) arr[P1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysLatchElaboration, CycleDelayInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic d, q;\n"
      "  always_latch begin\n"
      "    ##3 q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, ForkJoinArmAssignmentLeavesNothingLatched) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q = d;\n"
      "    fork q = d; join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_latch does not infer latched behavior", 3,
                              "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, AVariableACalledFunctionAssignsIsADriver) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, y, z;\n"
      "  function automatic logic g();\n"
      "    y = a;\n"
      "    return a;\n"
      "  endfunction\n"
      "  always_latch if (en) z = g();\n"
      "  assign y = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'y' driven by always_latch and continuous assignment", 7,
      "10.3.2"));
}

TEST(AlwaysLatchElaboration, AVariableACalledTaskAssignsIsNoDriver) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, y, z;\n"
      "  task automatic t();\n"
      "    y = a;\n"
      "  endtask\n"
      "  always_latch if (en) begin\n"
      "    t();\n"
      "    z = a;\n"
      "  end\n"
      "  initial y = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysLatchElaboration, NonblockingIntraAssignmentTimingAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= #1 d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
