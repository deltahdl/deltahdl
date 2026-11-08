#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_cb_invocations = 0;
const s_cb_data* g_cb_seen_data = nullptr;
int g_cb_seen_reason = 0;
void* g_cb_seen_user_data = nullptr;

int RecordingCb(s_cb_data* data) {
  ++g_cb_invocations;
  g_cb_seen_data = data;
  if (data) {
    g_cb_seen_reason = data->reason;
    g_cb_seen_user_data = data->user_data;
  }
  return 0;
}

int ReturningCb(s_cb_data*) { return 42; }

class VpiCallbackSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiCallbackSim, RegisterCbReturnsCallbackObjectHandle) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiType, h), vpiCallback);
}

TEST_F(VpiCallbackSim, RegisterCbStmt) {
  VpiObject stmt;
  stmt.type = vpiAssignment;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = VpiHandleOf(&stmt);
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, cbStmt);
}

TEST_F(VpiCallbackSim, RemoveCbMarksRemoved) {
  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = VpiHandleOf(&watched);
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  int result = vpi_remove_cb(h);
  EXPECT_EQ(result, 1);

  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].reason, -1);
}

TEST_F(VpiCallbackSim, RemoveCbNullReturnsZero) {
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);
}

TEST_F(VpiCallbackSim, RegisterCbNullDataReturnsNull) {
  EXPECT_EQ(vpi_register_cb(nullptr), nullptr);
}

TEST_F(VpiCallbackSim, RegisterCbStoresCbRtn) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().cb_rtn, &RecordingCb);
}

TEST_F(VpiCallbackSim, ExecuteCallbackInvokesCbRtnWithCbData) {
  g_cb_invocations = 0;
  g_cb_seen_data = nullptr;
  g_cb_seen_reason = 0;

  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  vpi_ctx_.ExecuteCallback(VpiObjectOf(h));

  EXPECT_EQ(g_cb_invocations, 1);
  EXPECT_NE(g_cb_seen_data, nullptr);
  EXPECT_EQ(g_cb_seen_reason, cbEndOfSimulation);
}

TEST_F(VpiCallbackSim, ExecuteCallbackWithoutCbRtnDoesNothing) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(VpiObjectOf(h)), 0);
}

TEST_F(VpiCallbackSim, ExecuteCallbackPropagatesCbRtnResult) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &ReturningCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(VpiObjectOf(h)), 42);
}

TEST_F(VpiCallbackSim, ExecuteCallbackPassesRegisteredUserData) {
  g_cb_invocations = 0;
  g_cb_seen_user_data = nullptr;

  int payload = 7;
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  vpi_ctx_.ExecuteCallback(VpiObjectOf(h));
  EXPECT_EQ(g_cb_seen_user_data, &payload);
}

TEST_F(VpiCallbackSim, ExecuteCallbackNullHandleReturnsZero) {
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(nullptr), 0);
}

TEST_F(VpiCallbackSim, ExecuteCallbackNonCallbackHandleReturnsZero) {
  sim_ctx_.CreateVariable("sig", 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle var_handle = vpi_handle_by_name(VpiText("sig"), nullptr);
  ASSERT_NE(var_handle, nullptr);
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(VpiObjectOf(var_handle)), 0);
}

TEST_F(VpiCallbackSim, CbValueChangeWithWatcherFires) {
  auto* var = sim_ctx_.CreateVariable("sig", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("sig"), nullptr);
  ASSERT_NE(h, nullptr);

  bool fired = false;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = h;
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&fired);
  vpi_ctx_.RegisterCbValueChange(cb);

  var->value = MakeLogic4VecVal(arena_, 1, 1);
  var->NotifyWatchers();
  EXPECT_TRUE(fired);
}

}  // namespace
}  // namespace delta
