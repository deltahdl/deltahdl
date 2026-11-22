#include <gtest/gtest.h>

#include <set>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_stmt_callbacks.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct StmtObject {
  int type;
  const char* label;
};

constexpr StmtObject kStatementClassObjects[] = {
    {vpiBegin, "begin"},
    {vpiNamedBegin, "named begin"},
    {vpiFork, "fork"},
    {vpiNamedFork, "named fork"},
    {vpiIf, "if"},
    {vpiIfElse, "if-else"},
    {vpiWhile, "while"},
    {vpiRepeat, "repeat"},
    {vpiFor, "for"},
    {vpiForever, "forever"},
    {vpiWait, "wait"},
    {vpiCase, "case"},
    {vpiAssignment, "assignment"},
    {vpiAssignStmt, "assign statement"},
    {vpiDeassign, "deassign"},
    {vpiDisable, "disable"},
    {vpiForce, "force"},
    {vpiRelease, "release"},
    {vpiEventStmt, "event statement"},
    {vpiDelayControl, "delay control"},
    {vpiEventControl, "event control"},
    {vpiTaskCall, "task call"},
    {vpiSysTaskCall, "system-task call"},
};

class VpiStmtCallbackByType : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  vpiHandle MakeHandleOfType(const char* name, int type) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(VpiText(name), nullptr);
    if (h) VpiObjectOf(h)->type = type;
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiStmtCallbackByType, EveryStatementClassObjectQualifies) {
  int suffix = 0;
  for (const StmtObject& obj : kStatementClassObjects) {
    std::string name = "s" + std::to_string(suffix++);
    vpiHandle stmt = MakeHandleOfType(name.c_str(), obj.type);
    ASSERT_NE(stmt, nullptr) << obj.label;

    s_cb_data cb = {};
    cb.reason = cbStmt;
    cb.obj = stmt;
    EXPECT_NE(vpi_register_cb(&cb), nullptr)
        << "Table 38-6 object '" << obj.label << "' should qualify for cbStmt";
  }
}

TEST_F(VpiStmtCallbackByType, ObjectOutsideTheStatementClassDoesNotQualify) {
  vpiHandle reg = MakeHandleOfType("v", vpiReg);
  ASSERT_NE(reg, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = reg;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

TEST_F(VpiStmtCallbackByType, ModuleInstanceRemainsAllowedInTheObjField) {
  vpiHandle mod = MakeHandleOfType("m", vpiModule);
  ASSERT_NE(mod, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = mod;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(StmtCallbacksOfARun, EachBlockIsCalledOnceBeforeItsContents) {
  RunWatchingTop(
      "module top; int a, b, c, d;\n"
      "  initial begin\n"
      "    begin : nb a = 1; end\n"
      "    fork b = 2; c = 3; join\n"
      "    fork : nf d = 4; join\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(StmtTypesCalled(),
            (std::vector<int>{vpiBegin, vpiNamedBegin, vpiAssignment, vpiFork,
                              vpiAssignment, vpiAssignment, vpiNamedFork,
                              vpiAssignment}));
}

constexpr const char* kNoteAndPass =
    "  function int f(int v); a = v; return v; endfunction\n";

TEST_F(StmtCallbacksOfARun,
       DISABLED_AStatementOfAFunctionInAnExpressionIsCalled) {
  RunWatchingTop(std::string("module top; int a, b;\n") + kNoteAndPass +
                 "  initial b = f(1);\n"
                 "endmodule\n");
  EXPECT_EQ(StmtTypesCalled(),
            (std::vector<int>{vpiAssignment, vpiAssignment, vpiReturn}));
}

TEST_F(StmtCallbacksOfARun,
       DISABLED_AnIfIsCalledBeforeItsConditionIsEvaluated) {
  RunWatchingTop(std::string("module top; int a, b;\n") + kNoteAndPass +
                 "  initial begin\n"
                 "    if (f(1)) b = 1;\n"
                 "    if (f(0)) b = 2; else b = 3;\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_EQ(StmtTypesCalled(),
            (std::vector<int>{vpiBegin, vpiIf, vpiAssignment, vpiReturn,
                              vpiAssignment, vpiIfElse, vpiAssignment,
                              vpiReturn, vpiAssignment}));
}

TEST_F(StmtCallbacksOfARun,
       DISABLED_AWhileIsCalledBeforeEachConditionEvaluation) {
  RunWatchingTop(std::string("module top; int a, i = 1;\n") + kNoteAndPass +
                 "  initial while (f(i)) begin i = i + 1; if (i == 3) break; "
                 "end\n"
                 "endmodule\n");
  EXPECT_EQ(
      StmtTypesCalled(),
      (std::vector<int>{vpiWhile, vpiAssignment, vpiReturn, vpiBegin,
                        vpiAssignment, vpiIf, vpiWhile, vpiAssignment,
                        vpiReturn, vpiBegin, vpiAssignment, vpiIf, vpiBreak}));
}

std::set<int> LoopShape() {
  return {vpiRepeat, vpiForever, vpiFor, vpiBegin, vpiIf, vpiBreak};
}

std::string LoopOf(const char* head) {
  return std::string("module top; int i;\n  initial ") + head +
         " begin i = i + 1; if (i == 2) break; end\nendmodule\n";
}

TEST_F(StmtCallbacksOfARun,
       DISABLED_ARepeatIsCalledOnEntryAndOnEachLaterIteration) {
  RunWatchingTop(LoopOf("repeat (5)"));
  EXPECT_EQ(StmtTypesCalledAmong(LoopShape()),
            (std::vector<int>{vpiRepeat, vpiBegin, vpiIf, vpiRepeat, vpiBegin,
                              vpiIf, vpiBreak}));
}

TEST_F(StmtCallbacksOfARun,
       DISABLED_AForeverIsCalledOnEntryAndOnEachLaterIteration) {
  RunWatchingTop(LoopOf("forever"));
  EXPECT_EQ(StmtTypesCalledAmong(LoopShape()),
            (std::vector<int>{vpiForever, vpiBegin, vpiIf, vpiForever, vpiBegin,
                              vpiIf, vpiBreak}));
}

TEST_F(StmtCallbacksOfARun,
       DISABLED_AForIsCalledFirstAndThenBeforeEachIncrement) {
  RunWatchingTop(
      "module top; int i;\n"
      "  initial for (i = 0; i < 5; i = i + 1) begin if (i == 2) break; end\n"
      "endmodule\n");
  EXPECT_EQ(StmtTypesCalledAmong(LoopShape()),
            (std::vector<int>{vpiFor, vpiBegin, vpiIf, vpiFor, vpiBegin, vpiIf,
                              vpiFor, vpiBegin, vpiIf, vpiBreak}));
}

TEST_F(StmtCallbacksOfARun, EachOtherStatementIsCalledJustBeforeItRuns) {
  RunWatchingTop(
      "module top; logic r; int a, b; event e;\n"
      "  initial begin\n"
      "    wait (a == 0);\n"
      "    case (a) 0: b = 1; default: b = 2; endcase\n"
      "    assign r = 1;\n"
      "    deassign r;\n"
      "    force b = 5;\n"
      "    release b;\n"
      "    -> e;\n"
      "    begin : blk disable blk; end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(
      StmtTypesCalled(),
      (std::vector<int>{vpiBegin, vpiWait, vpiNullStmt, vpiCase, vpiAssignment,
                        vpiAssignStmt, vpiDeassign, vpiForce, vpiRelease,
                        vpiEventStmt, vpiNamedBegin, vpiDisable}));
}

TEST_F(StmtCallbacksOfARun, ATimingControlIsCalledWhenReachedNotWhenDone) {
  RunWatchingTop(
      "module kick; initial #7 -> top.e; endmodule\n"
      "module top; int a, b; event e; kick k();\n"
      "  initial begin #5 a = 1; @(e) b = 1; end\n"
      "endmodule\n");
  EXPECT_EQ(StmtCalls(), (std::vector<StmtCall>{{vpiBegin, 0},
                                                {vpiDelayControl, 0},
                                                {vpiAssignment, 5},
                                                {vpiEventControl, 5},
                                                {vpiAssignment, 7}}));
}

TEST_F(StmtCallbacksOfARun, ATaskCallIsCalledBeforeTheTaskRuns) {
  RunWatchingTop(
      "module top; int a;\n"
      "  task tk; a = 1; endtask\n"
      "  initial begin tk; $noop; end\n"
      "endmodule\n");
  EXPECT_EQ(
      StmtTypesCalled(),
      (std::vector<int>{vpiBegin, vpiTaskCall, vpiAssignment, vpiSysTaskCall}));
}

}  // namespace
}  // namespace delta
