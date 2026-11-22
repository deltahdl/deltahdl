#include <gtest/gtest.h>

#include <csignal>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_38_39_fired = 0;
int CountingCb(s_cb_data*) {
  ++g_38_39_fired;
  return 0;
}

int g_38_39_fired_other = 0;
int OtherCountingCb(s_cb_data*) {
  ++g_38_39_fired_other;
  return 0;
}

class VpiRemoveCbSim : public ::testing::Test {
 protected:
  void SetUp() override {
    g_38_39_fired = 0;
    g_38_39_fired_other = 0;
    watched_.type = vpiReg;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  static vpiHandle RegisterCounting(int reason, VpiObject* on, int index = 0) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &CountingCb;
    cb.obj = VpiHandleOf(on);
    cb.index = index;
    return vpi_register_cb(&cb);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
  VpiObject watched_;
};

TEST_F(VpiRemoveCbSim, RemovesRegisteredCallbackAndReturnsOne) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &CountingCb;
  cb.obj = VpiHandleOf(&watched_);
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  ASSERT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 1);
  ASSERT_EQ(g_38_39_fired, 1);

  EXPECT_EQ(vpi_remove_cb(h), 1);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 0);
  EXPECT_EQ(g_38_39_fired, 1);
}

TEST_F(VpiRemoveCbSim, RemovesOnlyTheTargetedCallback) {
  s_cb_data cb_a = {};
  cb_a.reason = cbValueChange;
  cb_a.cb_rtn = &CountingCb;
  cb_a.obj = VpiHandleOf(&watched_);
  vpiHandle ha = vpi_register_cb(&cb_a);
  ASSERT_NE(ha, nullptr);

  s_cb_data cb_b = {};
  cb_b.reason = cbValueChange;
  cb_b.cb_rtn = &OtherCountingCb;
  cb_b.obj = VpiHandleOf(&watched_);
  vpiHandle hb = vpi_register_cb(&cb_b);
  ASSERT_NE(hb, nullptr);

  EXPECT_EQ(vpi_remove_cb(ha), 1);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 1);
  EXPECT_EQ(g_38_39_fired, 0);
  EXPECT_EQ(g_38_39_fired_other, 1);
}

TEST_F(VpiRemoveCbSim, NonCallbackHandleReturnsZero) {
  sim_ctx_.CreateVariable("n", 8);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle net = vpi_handle_by_name(VpiText("n"), nullptr);
  ASSERT_NE(net, nullptr);

  EXPECT_EQ(vpi_remove_cb(net), 0);
}

TEST_F(VpiRemoveCbSim, NullHandleReturnsZero) {
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);
}

TEST_F(VpiRemoveCbSim, HandleIsNoLongerValidAfterRemoval) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  EXPECT_EQ(vpi_remove_cb(h), 1);
  EXPECT_EQ(vpi_remove_cb(h), 0);
}

TEST_F(VpiRemoveCbSim, ASystfHandleIsNotRemoved) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &CountingCb;
  cb.obj = VpiHandleOf(&watched_);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$a_task");
  vpiHandle tf = vpi_register_systf(&task);
  ASSERT_NE(tf, nullptr);

  EXPECT_EQ(vpi_remove_cb(tf), 0);
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 1);
  EXPECT_EQ(g_38_39_fired, 1);
}

TEST_F(VpiRemoveCbSim, AModuleWideStatementCallbackIsRemovedByItsOneHandle) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  for (const char* name : {"m.a", "m.b"}) {
    VpiHandle stmt = vpi_ctx_.CreateModule(name, name);
    stmt->type = vpiAssignment;
    module->children.push_back(stmt);
  }
  vpiHandle h = RegisterCounting(cbStmt, module);
  ASSERT_NE(h, nullptr);
  ASSERT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt), 2);

  EXPECT_EQ(vpi_remove_cb(h), 1);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt), 0);
  EXPECT_EQ(g_38_39_fired, 2);
}

TEST_F(VpiRemoveCbSim, ARemovedSignalCallbackIsNotCalledWhenItsSignalIsRaised) {
  vpiHandle removed = RegisterCounting(cbSignal, nullptr, SIGINT);
  s_cb_data kept_data = {};
  kept_data.reason = cbSignal;
  kept_data.cb_rtn = &OtherCountingCb;
  kept_data.index = SIGINT;
  vpiHandle kept = vpi_register_cb(&kept_data);
  ASSERT_NE(removed, nullptr);
  ASSERT_NE(kept, nullptr);

  EXPECT_EQ(vpi_remove_cb(removed), 1);
  std::raise(SIGINT);

  EXPECT_EQ(vpi_ctx_.DeliverRaisedSignals(), 1);
  EXPECT_EQ(g_38_39_fired, 0);
  EXPECT_EQ(g_38_39_fired_other, 1);
  EXPECT_EQ(vpi_remove_cb(kept), 1);
}

TEST_F(VpiRemoveCbSim, DISABLED_CbInfoOfARemovedCallbackFillsNothingIn) {
  vpiHandle h = RegisterCounting(cbValueChange, &watched_);
  ASSERT_NE(h, nullptr);
  s_cb_data live = {};
  vpi_get_cb_info(h, &live);
  ASSERT_EQ(live.reason, cbValueChange);
  ASSERT_EQ(vpi_remove_cb(h), 1);

  s_cb_data stale = {};
  stale.reason = cbEndOfCompile;
  vpi_get_cb_info(h, &stale);

  EXPECT_EQ(stale.reason, cbEndOfCompile);
  EXPECT_EQ(stale.cb_rtn, nullptr);
  EXPECT_EQ(stale.obj, nullptr);
}

TEST_F(VpiRemoveCbSim, DISABLED_TheTypeOfARemovedCallbackIsAnError) {
  vpiHandle h = RegisterCounting(cbValueChange, &watched_);
  ASSERT_NE(h, nullptr);
  ASSERT_EQ(vpi_get(vpiType, h), vpiCallback);
  ASSERT_EQ(vpi_remove_cb(h), 1);

  const PLI_INT32 kType = vpi_get(vpiType, h);
  const PLI_INT32 kError = vpi_chk_error(nullptr);

  EXPECT_EQ(kType, vpiUndefined);
  EXPECT_NE(kError, 0);
}

const int kSimTimeReasons[] = {
    cbAtStartOfSimTime, cbNBASynch,    cbReadWriteSynch, cbAtEndOfSimTime,
    cbReadOnlySynch,    cbNextSimTime, cbAfterDelay,
};

std::vector<std::string>& TimeLabels() {
  static std::vector<std::string> labels;
  return labels;
}

PLI_INT32 RecordTimeLabel(p_cb_data cb) {
  TimeLabels().emplace_back(cb->user_data);
  return 0;
}

vpiHandle PlaceAtFive(int reason, const char* label) {
  static s_vpi_time time;
  time.type = vpiSimTime;
  time.high = 0;
  time.low = 5;
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &RecordTimeLabel;
  data.time = &time;
  data.user_data = VpiText(label);
  return vpi_register_cb(&data);
}

std::vector<PLI_INT32>& RemovalResults() {
  static std::vector<PLI_INT32> results;
  return results;
}

PLI_INT32 PlaceTimeCallbacksAndRemoveOneOfEach(p_cb_data) {
  for (const int kReason : kSimTimeReasons) {
    vpiHandle removed = PlaceAtFive(kReason, "removed");
    PlaceAtFive(kReason, "kept");
    RemovalResults().push_back(vpi_remove_cb(removed));
  }
  return 0;
}

class RemovedCallbacksOfARun : public VpiDesignRun {};

TEST_F(RemovedCallbacksOfARun, ARemovedTimeCallbackIsNeverCalled) {
  TimeLabels().clear();
  RemovalResults().clear();
  s_cb_data arm = {};
  arm.reason = cbStartOfSimulation;
  arm.cb_rtn = &PlaceTimeCallbacksAndRemoveOneOfEach;
  ASSERT_NE(vpi_register_cb(&arm), nullptr);

  Run("module top; timeunit 1ns; timeprecision 1ns; int q;\n"
      "  initial begin #5; q <= 1; #5; end\n"
      "endmodule\n");

  EXPECT_EQ(RemovalResults(), std::vector<PLI_INT32>(7, 1));
  EXPECT_EQ(TimeLabels(), std::vector<std::string>(7, "kept"));
}

}  // namespace
}  // namespace delta
