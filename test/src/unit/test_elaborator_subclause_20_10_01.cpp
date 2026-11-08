#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ElabSeverityTask, FatalBlocksSimulation) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(0, \"abort\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->simulation_blocked);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm': abort", 2,
                            "20.10.1"));
}

TEST(ElabSeverityTask, WarningDoesNotBlockSimulation) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $warning(\"heads up\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, InfoDoesNotBlockSimulation) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"hello\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, NoTaskKeepsSimulationUnblocked) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, NonConstantArgumentRejected) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  $error(\"x=%0d\", x);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "argument to $error must be a constant expression",
                            3, "20.10.1"));
}

TEST(ElabSeverityTask, ConstantArgumentAccepted) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int P = 7;\n"
      "  $info(\"p=%0d\", P);\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
}

TEST(ElabSeverityTask, GenerateIfFalseBranchSkipsTask) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int FAIL = 0;\n"
      "  if (FAIL) begin\n"
      "    $error(\"never\");\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, GenerateIfTrueBranchExecutesFatal) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int FAIL = 1;\n"
      "  if (FAIL) begin\n"
      "    $fatal(1, \"reached\");\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->simulation_blocked);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm.genblk1': reached",
                            4, "20.10.1"));
}

TEST(ElabSeverityTask, GenerateIfElseExecutesOnlyTaken) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int PICK = 0;\n"
      "  if (PICK) begin\n"
      "    $fatal(1);\n"
      "  end else begin\n"
      "    $info(\"ok\");\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, ErrorDoesNotAbortElaboration) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $error(\"keep going\");\n"
      "  wire after_error;\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (const auto& net : design->top_modules[0]->nets) {
    if (net.name == "after_error") {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found);
  EXPECT_TRUE(design->simulation_blocked);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration ERROR in scope 'm': keep going", 2,
                            "20.10.1"));
}

TEST(ElabSeverityTask, FatalMessageRecordsSeverityTag) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(1, \"boom\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity, "FATAL");
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm': boom", 2,
                            "20.10.1"));
}

TEST(ElabSeverityTask, ErrorMessageRecordsSeverityTag) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $error(\"oops\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity, "ERROR");
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration ERROR in scope 'm': oops", 2,
                            "20.10.1"));
}

TEST(ElabSeverityTask, WarningMessageRecordsSeverityTag) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $warning(\"careful\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity, "WARNING");
}

TEST(ElabSeverityTask, InfoMessageRecordsSeverityTag) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"fyi\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity, "INFO");
}

TEST(ElabSeverityTask, MessageRecordsCallSiteFileAndLine) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $error(\"here\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_NE(design->last_elab_severity_loc.file_id, 0u);
  EXPECT_EQ(design->last_elab_severity_loc.line, 2u);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration ERROR in scope 'm': here", 2,
                            "20.10.1"));
}

TEST(ElabSeverityTask, MessageRecordsHierarchicalScope) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module top;\n"
      "  $info(\"hi\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity_scope, "top");
}

TEST(ElabSeverityTask, GenerateScopeAppearsInMessageScope) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module top;\n"
      "  for (genvar i = 0; i < 1; i++) begin\n"
      "    $info(\"hi\");\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity_scope, "top.genblk1_0");
}

TEST(ElabSeverityTask, MessageRecordsUserDefinedText) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $error(\"parameter out of range\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity_msg, "parameter out of range");
  EXPECT_TRUE(ReportedError(
      ef.diag.Diagnostics(),
      "elaboration ERROR in scope 'm': parameter out of range", 2, "20.10.1"));
}

TEST(ElabSeverityTask, NoUserMessageLeavesBodyEmpty) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $info;\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity, "INFO");
  EXPECT_TRUE(design->last_elab_severity_msg.empty());
}

TEST(ElabSeverityTask, FatalMessageRecordsUserDefinedText) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(1, \"aborting now\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity_msg, "aborting now");
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm': aborting now", 2,
                            "20.10.1"));
}

TEST(ElabSeverityTask, GenerateForZeroIterationsSkipsTask) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 0; i++) begin\n"
      "    $fatal(1, \"never\");\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, GenerateForExecutesTaskOnIteration) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 1; i++) begin\n"
      "    $fatal(1, \"reached\");\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->simulation_blocked);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm.genblk1_0': reached",
                            3, "20.10.1"));
}

TEST(ElabSeverityTask, ConstantBinaryExpressionArgumentAccepted) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int A = 3;\n"
      "  parameter int B = 4;\n"
      "  $info(\"sum=%0d\", A + B);\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
}

TEST(ElabSeverityTask, ConstantFunctionCallArgumentAccepted) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter logic [7:0] P = 8'd5;\n"
      "  $info(\"w=%0d\", $bits(P));\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
}

TEST(ElabSeverityTask, NonConstantArgInFatalRejected) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  $fatal(1, \"x=%0d\", x);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "argument to $fatal must be a constant expression",
                            3, "20.10.1"));
}

TEST(ElabSeverityTask, FatalInsideProcedureDoesNotBlockSimulation) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  initial $fatal(1, \"runtime\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
  EXPECT_FALSE(design->simulation_blocked);
  EXPECT_TRUE(design->last_elab_severity.empty());
}

TEST(ElabSeverityTask, LiteralArgumentAccepted) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"v=%0d\", 42);\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
  EXPECT_EQ(design->last_elab_severity, "INFO");
}

TEST(ElabSeverityTask, GenerateCaseSelectedBranchExecutesFatal) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int SEL = 1;\n"
      "  case (SEL)\n"
      "    0: begin $info(\"zero\"); end\n"
      "    1: begin $fatal(1, \"one\"); end\n"
      "  endcase\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->simulation_blocked);
  EXPECT_EQ(design->last_elab_severity, "FATAL");
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm.genblk1': one", 5,
                            "20.10.1"));
}

TEST(ElabSeverityTask, GenerateCaseUnselectedBranchSkipsTask) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int SEL = 0;\n"
      "  case (SEL)\n"
      "    1: begin $fatal(1, \"one\"); end\n"
      "    default: begin $info(\"picked default\"); end\n"
      "  endcase\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
  EXPECT_EQ(design->last_elab_severity, "INFO");
}

TEST(ElabSeverityTask, LocalparamArgumentAccepted) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int LP = 12;\n"
      "  $info(\"lp=%0d\", LP);\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
  EXPECT_EQ(design->last_elab_severity, "INFO");
}

TEST(ElabSeverityTask, GenvarArgumentAcceptedInGenerateFor) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin\n"
      "    $info(\"branch %0d generated\", i);\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ef.has_errors);
  EXPECT_EQ(design->last_elab_severity, "INFO");
  EXPECT_FALSE(design->simulation_blocked);
}

TEST(ElabSeverityTask, GenvarInCompoundArgAcceptedAndFatalExecutes) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 1; i++) begin\n"
      "    $fatal(1, \"idx=%0d\", i + 1);\n"
      "  end\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(), "idx=1", 3, "20.10.1"));
  EXPECT_FALSE(ReportedError(ef.diag.Diagnostics(),
                             "argument to $fatal must be a constant expression",
                             3, "20.10.1"));
  EXPECT_TRUE(design->simulation_blocked);
}

TEST(ElabSeverityTask, NonConstantStillRejectedAfterGenerateFor) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 1; i++) begin\n"
      "    $info(\"ok %0d\", i);\n"
      "  end\n"
      "  logic [7:0] y;\n"
      "  $error(\"y=%0d\", y);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "argument to $error must be a constant expression",
                            6, "20.10.1"));
}

TEST(ElabSeverityTask, ErrorAndFatalAreReportedAsErrors) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  $error(\"oops\");\n"
      "  $fatal(1, \"boom\");\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration ERROR in scope 'm': oops", 2,
                            "20.10.1"));
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm': boom", 3,
                            "20.10.1"));
}

TEST(ElabSeverityTask, WarningAndInfoAreReportedAsWarnings) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  $warning(\"careful\");\n"
      "  $info(\"fyi\");\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedWarning(ef.diag.Diagnostics(),
                              "elaboration WARNING in scope 'm': careful", 2,
                              "20.10.1"));
  EXPECT_TRUE(ReportedWarning(ef.diag.Diagnostics(),
                              "elaboration INFO in scope 'm': fyi", 3,
                              "20.10.1"));
  EXPECT_FALSE(ef.diag.HasErrors());
}

TEST(ElabSeverityTask, MessageFormatsItsConstantArguments) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  parameter P = 5;\n"
      "  $warning(\"P=%0d h=%h\", P, 8'hab);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedWarning(ef.diag.Diagnostics(),
                              "elaboration WARNING in scope 'm': P=5 h=ab", 3,
                              "20.10.1"));
}

TEST(ElabSeverityTask, MessageSizesADecimalByTheArgumentsWidth) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  parameter logic [3:0] P = 5;\n"
      "  $info(\"[%d]\", P);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedWarning(ef.diag.Diagnostics(),
                              "elaboration INFO in scope 'm': [ 5]", 3,
                              "20.10.1"));
}

TEST(ElabSeverityTask, MessageFormatsAnArgumentWiderThanSixtyFourBits) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  $info(\"%h\", 72'h12_3456789a_bcdef012);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ReportedWarning(
      ef.diag.Diagnostics(),
      "elaboration INFO in scope 'm': 123456789abcdef012", 2, "20.10.1"));
}

}  // namespace
