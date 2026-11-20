#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SystemTaskPlaces : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

int g_task_calls = 0;

PLI_INT32 CountTaskCall(PLI_BYTE8*) {
  ++g_task_calls;
  return 0;
}

void RunWithTheTask(const std::string& src, SimFixture& f) {
  g_task_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$t");
  task.calltf = CountTaskCall;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return;
  LowerAndRun(design, f);
  f.scheduler.EndSimulation();
}

int CallsOfTheTaskIn(const std::string& src) {
  SimFixture f;
  RunWithTheTask(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return g_task_calls;
}

void ExpectTheTaskRefusedIn(const std::string& src) {
  SimFixture f;
  RunWithTheTask(src, f);
  EXPECT_EQ(g_task_calls, 0);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$t is a user-defined system task and returns no "
                            "value, so it cannot be used as an expression",
                            LineHolding(src, "$t"), "36.5"));
}

std::string Module(const std::string& body) {
  return "module m;\n  int r;\n" + body + "endmodule\n";
}

TEST_F(SystemTaskPlaces, AStatementInAnAlwaysProcedureRunsTheTask) {
  EXPECT_EQ(CallsOfTheTaskIn(Module("  logic clk = 0;\n"
                                    "  always @(clk) $t;\n"
                                    "  initial #1 clk = 1;\n")),
            1);
}

TEST_F(SystemTaskPlaces, AStatementInAnAlwaysCombProcedureRunsTheTask) {
  EXPECT_GE(CallsOfTheTaskIn(Module("  always_comb if (r >= 0) $t;\n")), 1);
}

TEST_F(SystemTaskPlaces, AStatementInAFinalProcedureRunsTheTask) {
  EXPECT_EQ(CallsOfTheTaskIn(Module("  final $t;\n")), 1);
}

TEST_F(SystemTaskPlaces, AStatementInACheckerRunsTheTask) {
  EXPECT_EQ(CallsOfTheTaskIn("checker c;\n"
                             "  final $t;\n"
                             "endchecker\n"
                             "module m; c u (); endmodule\n"),
            1);
}

TEST_F(SystemTaskPlaces, AStatementInAGenerateBlockRunsTheTask) {
  EXPECT_EQ(CallsOfTheTaskIn(Module("  if (1) begin : g\n"
                                    "    initial $t;\n"
                                    "  end\n")),
            1);
}

TEST_F(SystemTaskPlaces, AStatementInACompilationUnitSubroutineRunsTheTask) {
  EXPECT_EQ(CallsOfTheTaskIn("function void cu(); $t; endfunction\n"
                             "module m; initial cu(); endmodule\n"),
            1);
}

TEST_F(SystemTaskPlaces, AContinuousAssignmentRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  wire [31:0] w;\n  assign w = $t;\n"));
}

TEST_F(SystemTaskPlaces, ADeclarationInitializerRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  int v = $t;\n"));
}

TEST_F(SystemTaskPlaces, AnOperandOfALargerExpressionRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial r = $t + 1;\n"));
}

TEST_F(SystemTaskPlaces, AnIfConditionRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial if ($t) r = 1;\n"));
}

TEST_F(SystemTaskPlaces, AWhileConditionRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial while ($t) r = 1;\n"));
}

TEST_F(SystemTaskPlaces, AForConditionRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial for (int i = 0; $t; i++) r = 1;\n"));
}

TEST_F(SystemTaskPlaces, ADoWhileConditionRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial do r = 1; while ($t);\n"));
}

TEST_F(SystemTaskPlaces, ARepeatCountRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial repeat ($t) r = 1;\n"));
}

TEST_F(SystemTaskPlaces, ACaseExpressionRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  initial case ($t) 1: r = 1; default: r = 2; endcase\n"));
}

TEST_F(SystemTaskPlaces, ACaseItemRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  initial case (r) $t: r = 1; default: r = 2; endcase\n"));
}

TEST_F(SystemTaskPlaces, AnArgumentOfASubroutineCallRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  function int g(int v); return v; endfunction\n"
             "  initial r = g($t);\n"));
}

TEST_F(SystemTaskPlaces, AnArgumentOfASystemCallRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial r = $clog2($t);\n"));
}

TEST_F(SystemTaskPlaces, TheOperandOfAVoidCastRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial void'($t);\n"));
}

TEST_F(SystemTaskPlaces, AReturnExpressionRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  function int g(); return $t; endfunction\n"
             "  initial r = g();\n"));
}

TEST_F(SystemTaskPlaces, APortConnectionRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      "module sub(input logic [31:0] a); endmodule\n"
      "module m; sub u (.a($t)); endmodule\n");
}

TEST_F(SystemTaskPlaces, APrimitiveTerminalRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  wire z;\n  or g (z, $t, 1'b0);\n"));
}

TEST_F(SystemTaskPlaces, AnEventControlRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  initial @($t) r = 1;\n"));
}

TEST_F(SystemTaskPlaces, DISABLED_AClockingEventRefusesTheTask) {
  ExpectTheTaskRefusedIn(Module("  clocking cb @(posedge $t); endclocking\n"));
}

TEST_F(SystemTaskPlaces, AConstraintRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  class C; rand int x; constraint c { x > $t; } endclass\n"
             "  C o;\n"
             "  initial begin o = new; void'(o.randomize()); end\n"));
}

TEST_F(SystemTaskPlaces, APropertyRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  logic clk = 0;\n"
             "  assert property (@(posedge clk) $t);\n"
             "  initial #1 clk = 1;\n"));
}

TEST_F(SystemTaskPlaces, AnExpressionInAClassMethodRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  class C; function int k(); return $t + 1; endfunction\n"
             "  endclass\n"
             "  C o;\n"
             "  initial begin o = new; r = o.k(); end\n"));
}

TEST_F(SystemTaskPlaces, AnExpressionInAPackageFunctionRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      "package p;\n"
      "  function int g(); return $t + 1; endfunction\n"
      "endpackage\n"
      "module m; int r; initial r = p::g(); endmodule\n");
}

TEST_F(SystemTaskPlaces, AnExpressionInAPackageTaskRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      "package p;\n"
      "  task k(output int v); v = $t + 1; endtask\n"
      "endpackage\n"
      "module m; int r; initial p::k(r); endmodule\n");
}

TEST_F(SystemTaskPlaces, AnExpressionInAModuleTaskRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  task k(); r = $t + 1; endtask\n"
             "  initial k();\n"));
}

TEST_F(SystemTaskPlaces, AnExpressionInAProgramRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      "program m;\n"
      "  int r;\n"
      "  initial r = $t;\n"
      "endprogram\n");
}

TEST_F(SystemTaskPlaces, AnExpressionInAnInterfaceRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      "interface ifc;\n"
      "  int r;\n"
      "  initial r = $t;\n"
      "endinterface\n"
      "module m; ifc u (); endmodule\n");
}

TEST_F(SystemTaskPlaces, AnExpressionInAGenerateBlockRefusesTheTask) {
  ExpectTheTaskRefusedIn(
      Module("  if (1) begin : g\n"
             "    initial r = $t;\n"
             "  end\n"));
}

}  // namespace
}  // namespace delta
