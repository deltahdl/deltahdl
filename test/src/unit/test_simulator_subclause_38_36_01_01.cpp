#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_stmt_calls = 0;
s_vpi_value* g_stmt_value = reinterpret_cast<s_vpi_value*>(1);
int g_stmt_index = -1;
s_vpi_time* g_stmt_time = reinterpret_cast<s_vpi_time*>(1);
s_vpi_time g_stmt_time_seen = {};

int RecordStmtCb(s_cb_data* data) {
  ++g_stmt_calls;
  if (data) {
    g_stmt_value = data->value;
    g_stmt_index = data->index;
    g_stmt_time = data->time;
    if (data->time) g_stmt_time_seen = *data->time;
  }
  return 0;
}

class VpiStmtCallback : public ::testing::Test {
 protected:
  void SetUp() override {
    g_stmt_calls = 0;
    g_stmt_value = reinterpret_cast<s_vpi_value*>(1);
    g_stmt_index = -1;
    g_stmt_time = reinterpret_cast<s_vpi_time*>(1);
    g_stmt_time_seen = s_vpi_time{};
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void AdvanceTo(uint64_t t) {
    auto* ev = scheduler_.GetEventPool().Acquire();
    ev->callback = []() {};
    scheduler_.ScheduleEvent(SimTime{t}, Region::kActive, ev);
    scheduler_.Run();
  }

  vpiHandle MakeStatementHandle(const char* name, bool protect) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(VpiText(name), nullptr);
    if (h) {
      VpiObjectOf(h)->type = vpiNamedBegin;
      VpiObjectOf(h)->is_protected = protect;
    }
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiStmtCallback, ProtectedStatementRejected) {
  vpiHandle stmt = MakeStatementHandle("p", true);
  ASSERT_NE(stmt, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = stmt;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

TEST_F(VpiStmtCallback, UnprotectedStatementAccepted) {
  vpiHandle stmt = MakeStatementHandle("u", false);
  ASSERT_NE(stmt, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = stmt;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiStmtCallback, ProtectedHandleRejectionIsSpecificToStmtReason) {
  vpiHandle stmt = MakeStatementHandle("s", true);
  ASSERT_NE(stmt, nullptr);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = stmt;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiStmtCallback,
       MultipleIdenticalRegistrationsProduceMultipleCallbacks) {
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.obj = MakeStatementHandle("m", false);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_stmt_calls, 2);
}

TEST_F(VpiStmtCallback, DispatchedDataHasNullValueAndZeroIndex) {
  s_vpi_value supplied_value = {};
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.obj = MakeStatementHandle("v", false);
  cb.value = &supplied_value;
  cb.index = 5;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  ASSERT_EQ(g_stmt_calls, 1);
  EXPECT_EQ(g_stmt_value, nullptr);
  EXPECT_EQ(g_stmt_index, 0);
}

TEST_F(VpiStmtCallback, SuppressTimeNullsDispatchedTimePointer) {
  s_vpi_time t = {};
  t.type = vpiSuppressTime;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.obj = MakeStatementHandle("n", false);
  cb.time = &t;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  ASSERT_EQ(g_stmt_calls, 1);
  EXPECT_EQ(g_stmt_time, nullptr);
}

TEST_F(VpiStmtCallback, DispatchedTimeCarriesTheCurrentSimulationTime) {
  AdvanceTo(37);

  s_vpi_time t = {};
  t.type = vpiSimTime;
  t.low = 5;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.obj = MakeStatementHandle("c", false);
  cb.time = &t;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  ASSERT_EQ(g_stmt_calls, 1);
  ASSERT_NE(g_stmt_time, nullptr);
  EXPECT_EQ(g_stmt_time_seen.type, vpiSimTime);
  EXPECT_EQ(g_stmt_time_seen.low, 37u);
  EXPECT_EQ(g_stmt_time_seen.high, 0u);
  EXPECT_NE(g_stmt_time, &t);
  EXPECT_EQ(t.low, 5u);
}

std::vector<int>& StmtsCalledBack() {
  static std::vector<int> kinds;
  return kinds;
}

PLI_INT32 RecordStmt(p_cb_data cb) {
  StmtsCalledBack().push_back(vpi_get(vpiType, cb->obj));
  return 0;
}

PLI_INT32 PlaceModuleWideCbStmt(p_cb_data) {
  s_cb_data data = {};
  data.reason = cbStmt;
  data.cb_rtn = &RecordStmt;
  data.obj = vpi_handle_by_name(VpiText("top"), nullptr);
  vpi_register_cb(&data);
  return 0;
}

class StmtCallbacksOfARun : public VpiDesignRun {};

TEST_F(StmtCallbacksOfARun, ACbStmtIsCalledBeforeEachStatementOfItsModule) {
  StmtsCalledBack().clear();
  s_cb_data data = {};
  data.reason = cbStartOfSimulation;
  data.cb_rtn = &PlaceModuleWideCbStmt;
  ASSERT_NE(vpi_register_cb(&data), nullptr);
  Run("module top; int a, b, c;\n"
      "  initial begin a = 1; b = 2; #1 c = 3; end\n"
      "endmodule\n");
  EXPECT_EQ(StmtsCalledBack(),
            (std::vector<int>{vpiBegin, vpiAssignment, vpiAssignment,
                              vpiDelayControl, vpiAssignment}));
}

TEST_F(StmtCallbacksOfARun, ACbStmtPassesOverADeclarationInABlock) {
  StmtsCalledBack().clear();
  s_cb_data data = {};
  data.reason = cbStartOfSimulation;
  data.cb_rtn = &PlaceModuleWideCbStmt;
  ASSERT_NE(vpi_register_cb(&data), nullptr);
  Run("module top; int a;\n"
      "  initial begin int x; x = 2; a = x; end\n"
      "endmodule\n");
  EXPECT_EQ(StmtsCalledBack(),
            (std::vector<int>{vpiBegin, vpiAssignment, vpiAssignment}));
}

}  // namespace
}  // namespace delta
