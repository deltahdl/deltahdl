#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FinalProcedureElaboration, DelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final #5 x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, EventControlInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  final @(posedge clk) x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, WaitInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final wait(x) x = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, ForkJoinInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  final begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "final procedure shall not contain fork-join statements", 3, "9.2.3"));
}

TEST(FinalProcedureElaboration, ValidFinalBlockNoErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  final begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, ElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kFinal) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(FinalProcedureElaboration, MultipleFinalProcedures) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  final a = 1;\n"
      "  final b = 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  int count = 0;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kFinal) ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST(FinalProcedureElaboration, FinalAndInitialCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = 10;\n"
      "  final x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool has_initial = false, has_final = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kInitial) has_initial = true;
    if (p.kind == RtlirProcessKind::kFinal) has_final = true;
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_final);
}

TEST(FinalProcedureElaboration, WaitForkInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  final begin\n"
      "    wait fork;\n"
      "    a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, NestedDelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final begin\n"
      "    x = 0;\n"
      "    #1 x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, DelayInNestedIfErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final begin\n"
      "    if (x)\n"
      "      #1 x = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, DelayInCaseBranchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic x;\n"
      "  final begin\n"
      "    case (sel)\n"
      "      2'b00: #1 x = 0;\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            4, "9.2.3"));
}

TEST(FinalProcedureElaboration, CaseBranchWithoutTimingValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic x;\n"
      "  final begin\n"
      "    case (sel)\n"
      "      2'b00: x = 0;\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, IntraAssignDelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x = #5 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, IntraAssignEventControlInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  final x = @(posedge clk) y;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            4, "9.2.3"));
}

TEST(FinalProcedureElaboration, IntraAssignNonblockingDelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x <= #5 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            3, "9.2.3"));
}

TEST(FinalProcedureElaboration, IfStatementInFinalValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x, y;\n"
      "  final if (x) y = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, DisplayCallInFinalValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  final $display(\"statistics\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, FunctionCallInFinalValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int doubler(int a); return a * 2; endfunction\n"
      "  int x;\n"
      "  final x = doubler(21);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FinalProcedureElaboration, ATaskEnabledInAFinalProcedureIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  function int g(); return 1; endfunction\n"
      "  int x;\n"
      "  final begin x = 1; t(); end\n"
      "  final x = g();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure enables task 't'", 5, "9.2.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "final procedure enables", 6,
                             "9.2.3"));
}

TEST(FinalProcedureElaboration, ATaskEnabledByItsBareNameIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  final t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure enables task 't'", 3, "9.2.3"));
}

TEST(FinalProcedureElaboration, APackageOrUnitTaskEnabledIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package pk; task t; endtask endpackage\n"
      "task u; endtask\n"
      "module m;\n"
      "  final begin\n"
      "    pk::t();\n"
      "    u();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure enables task 'pk::t'", 5,
                            "9.2.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure enables task 'u'", 6, "9.2.3"));
}

}  // namespace
