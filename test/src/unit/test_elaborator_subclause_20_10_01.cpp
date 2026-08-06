#include "fixture_elaborator.h"

using namespace delta;

namespace {

// $fatal at module-item level executes during elaboration and shall block
// simulation from starting (§20.10.1).
TEST(ElabSeverityTask, FatalBlocksSimulation) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(0, \"abort\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->simulation_blocked);
}

// $warning at module-item level emits but does not block simulation
// (§20.10.1).
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

// $info at module-item level emits but does not block simulation (§20.10.1).
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

// A design with no elaboration severity tasks shall have simulation_blocked
// false (§20.10.1).
TEST(ElabSeverityTask, NoTaskKeepsSimulationUnblocked) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(design->simulation_blocked);
}

// §20.10.1 — list_of_arguments may only contain a formatting string and
// constant expressions. A non-constant argument shall be rejected.
TEST(ElabSeverityTask, NonConstantArgumentRejected) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  $error(\"x=%0d\", x);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ef.has_errors);
}

// §20.10.1 — a parameter reference qualifies as a constant expression and is
// accepted in the argument list.
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

// §20.10.1 — when a conditional generate construct selects the branch that
// does NOT contain the task, the task does not execute and simulation
// remains unblocked.
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

// §20.10.1 — when a conditional generate construct selects a branch that
// contains $fatal, the task executes and simulation is blocked.
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
}

// §20.10.1 — $fatal in one generate branch and $info in another: only the
// taken branch's task affects the design.
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

// §20.10.1 claim 11 — after $error executes, elaboration of subsequent items
// continues. A net declared after the $error must still appear in the
// elaborated model.
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
}

// §20.10.1 claim 13 — every elaboration severity task shall print a
// tool-specific message that identifies the severity level.
TEST(ElabSeverityTask, FatalMessageRecordsSeverityTag) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(1, \"boom\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity, "FATAL");
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

// §20.10.1 claim 13 — the file/line of the elaboration severity task call
// shall match `__FILE__`/`__LINE__` (per §22.13). The recorded SourceLoc
// must carry the call-site file id and line number.
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
}

// §20.10.1 claim 13 — the message shall include the hierarchical name of
// the scope in which the call is made. For a top module called `top` the
// scope name is at least `top`.
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

// §20.10.1 claim 13 — a call inside a generate-for block sits inside a
// nested scope; the hierarchical scope name shall reflect the generate
// block prefix in addition to the module name.
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
  EXPECT_NE(design->last_elab_severity_scope.find("top"), std::string::npos);
  EXPECT_NE(design->last_elab_severity_scope.find('i'), std::string::npos);
}

// §20.10.1 claim 14 — the tool-specific message shall include the
// user-defined message if specified. The recorded message body must carry
// the literal text the user supplied.
TEST(ElabSeverityTask, MessageRecordsUserDefinedText) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $error(\"parameter out of range\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity_msg, "parameter out of range");
}

// §20.10.1 claim 14 — when no user-defined message is supplied the message
// body remains empty.
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

// §20.10.1 claim 14 — the user-defined message rule applies to $fatal too:
// the supplied text after the finish_number must be recorded.
TEST(ElabSeverityTask, FatalMessageRecordsUserDefinedText) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(1, \"aborting now\");\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->last_elab_severity_msg, "aborting now");
}

// §20.10.1 claim 3 — a generate-for loop with zero iterations does not
// produce any surviving elaboration severity task call; simulation
// therefore remains unblocked.
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

// §20.10.1 claim 3 — a generate-for loop that iterates at least once causes
// the body's elaboration severity task to execute. Simulation must then be
// blocked when the task is $fatal.
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
}

// §20.10.1 claim 5 — a compound constant expression built from parameter
// references with a binary operator qualifies as a constant expression and
// must be accepted.
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

// §20.10.1 claim 5 — the LRM calls out that constant function calls are
// allowed in the argument list. $bits applied to a parameter is a
// constant system function call, so it must be accepted.
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

// §20.10.1 claim 5 — the constant-argument rule applies uniformly to all
// four severity tasks. A non-constant argument to $fatal must be rejected,
// not only to $error.
TEST(ElabSeverityTask, NonConstantArgInFatalRejected) {
  ElabFixture ef;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  $fatal(1, \"x=%0d\", x);\n"
      "endmodule\n",
      ef);
  EXPECT_TRUE(ef.has_errors);
}

// §20.10.1 — a severity task called from inside a procedure becomes a
// run-time severity task, so the elaborator must NOT treat it as an
// elaboration severity task: an `initial $fatal` therefore leaves simulation
// unblocked at elaboration (it would only fire if that process later runs).
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

// §20.10.1 claim 5 — a bare integer literal is a constant expression per
// §11.2.1 and takes a distinct constant-check path from a named reference
// (immediate literal vs. scope lookup). It must be accepted in the argument
// list.
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

// §20.10.1 — activation may be controlled by a generate-case (a conditional
// generate construct per §27.5). When the selector picks the branch holding
// $fatal, that task executes and blocks simulation.
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
}

// §20.10.1 — when the generate-case selector picks a branch that does not
// hold $fatal, the $fatal in the unselected branch never executes and
// simulation stays unblocked; only the taken branch's task runs.
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

// §20.10.1 claim 5 — a localparam is a constant expression per §11.2.1, so a
// localparam reference is accepted in the argument list just like a
// parameter.
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

// §20.10.1 claim 5 — a genvar is a constant expression per §11.2.1. The LRM's
// own Example 2 passes the loop genvar to $info from inside a generate-for
// (`$info("i = %0d branch generated", i)`). The genvar reference must be
// accepted, not rejected as a non-constant, and the task must still execute.
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

// §20.10.1 claim 5 — the genvar remains usable inside a compound constant
// expression in the argument list, and a $fatal that reaches it still blocks
// simulation (proving the task executed rather than being rejected).
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
  EXPECT_FALSE(ef.has_errors);
  EXPECT_TRUE(design->simulation_blocked);
}

// §20.10.1 claim 5 — the genvar overlay must not leak out of the generate
// body: a bare identifier that is neither a parameter nor an in-scope genvar
// is still rejected at plain module-item level after a generate-for closes.
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
  EXPECT_TRUE(ef.has_errors);
}

}  // namespace
