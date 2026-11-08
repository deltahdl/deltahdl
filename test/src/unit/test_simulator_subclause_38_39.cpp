#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
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

}  // namespace
}  // namespace delta
