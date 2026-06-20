#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36: the simulator executes a callback by invoking its cb_rtn and passing
// a pointer to the s_cb_data structure. This recorder lets a test observe the
// production code applying that contract.
int g_cb_invocations = 0;
const VpiCbData* g_cb_seen_data = nullptr;
int g_cb_seen_reason = 0;
void* g_cb_seen_user_data = nullptr;

int RecordingCb(VpiCbData* data) {
  ++g_cb_invocations;
  g_cb_seen_data = data;
  if (data) {
    g_cb_seen_reason = data->reason;
    g_cb_seen_user_data = data->user_data;
  }
  return 0;
}

// A routine that returns a recognizable value, so a test can confirm the
// simulator propagates the cb_rtn result back from executing the callback.
int ReturningCb(VpiCbData*) { return 42; }

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

TEST_F(VpiCallbackSim, RegisterCbReturnsHandle) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
}

TEST_F(VpiCallbackSim, RegisterCbStmt) {
  s_cb_data cb = {};
  cb.reason = cbStmt;
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, cbStmt);
}

TEST_F(VpiCallbackSim, RemoveCbMarksRemoved) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  int result = vpi_remove_cb(h);
  EXPECT_EQ(result, 1);

  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].reason, -1);
}

TEST_F(VpiCallbackSim, RemoveCbNullReturnsZero) {
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);
}

// §38.36: cb_data_p shall point to an s_cb_data structure. A null pointer is
// not a valid structure, so registration cannot produce a callback handle.
TEST_F(VpiCallbackSim, RegisterCbNullDataReturnsNull) {
  EXPECT_EQ(vpi_register_cb(nullptr), nullptr);
}

// §38.36 (Figure 38-17): the s_cb_data structure carries a cb_rtn field that
// shall be set to the application routine. vpi_register_cb() must preserve it.
TEST_F(VpiCallbackSim, RegisterCbStoresCbRtn) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().cb_rtn, &RecordingCb);
}

// §38.36: the cb_rtn shall be invoked when the simulator executes the callback,
// and the callback routine shall be passed a pointer to an s_cb_data structure.
TEST_F(VpiCallbackSim, ExecuteCallbackInvokesCbRtnWithCbData) {
  g_cb_invocations = 0;
  g_cb_seen_data = nullptr;
  g_cb_seen_reason = 0;

  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  vpi_ctx_.ExecuteCallback(h);

  EXPECT_EQ(g_cb_invocations, 1);
  EXPECT_NE(g_cb_seen_data, nullptr);
  EXPECT_EQ(g_cb_seen_reason, cbEndOfSimulation);
}

// §38.36: with no application routine set, the simulator has nothing to invoke
// when it executes the callback.
TEST_F(VpiCallbackSim, ExecuteCallbackWithoutCbRtnDoesNothing) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(h), 0);
}

// §38.36: the cb_rtn returns a value to the simulator; executing the callback
// shall hand that value back.
TEST_F(VpiCallbackSim, ExecuteCallbackPropagatesCbRtnResult) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &ReturningCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(h), 42);
}

// §38.36: the structure passed to the callback routine is the one supplied at
// registration, so application data placed in user_data reaches the routine.
TEST_F(VpiCallbackSim, ExecuteCallbackPassesRegisteredUserData) {
  g_cb_invocations = 0;
  g_cb_seen_user_data = nullptr;

  int payload = 7;
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  cb.user_data = &payload;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  vpi_ctx_.ExecuteCallback(h);
  EXPECT_EQ(g_cb_seen_user_data, &payload);
}

// §38.36: a null handle does not identify any callback, so the simulator has
// nothing to execute.
TEST_F(VpiCallbackSim, ExecuteCallbackNullHandleReturnsZero) {
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(nullptr), 0);
}

// §38.36: vpi_register_cb returns a handle to a callback object; a handle to
// any other kind of object does not name a callback to execute.
TEST_F(VpiCallbackSim, ExecuteCallbackNonCallbackHandleReturnsZero) {
  sim_ctx_.CreateVariable("sig", 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle var_handle = vpi_handle_by_name("sig", nullptr);
  ASSERT_NE(var_handle, nullptr);
  EXPECT_EQ(vpi_ctx_.ExecuteCallback(var_handle), 0);
}

TEST_F(VpiCallbackSim, CbValueChangeWithWatcherFires) {
  auto* var = sim_ctx_.CreateVariable("sig", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sig", nullptr);
  ASSERT_NE(h, nullptr);

  bool fired = false;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = h;
  cb.user_data = &fired;
  vpi_ctx_.RegisterCbValueChange(cb);

  var->value = MakeLogic4VecVal(arena_, 1, 1);
  var->NotifyWatchers();
  EXPECT_TRUE(fired);
}

}  // namespace
}  // namespace delta
