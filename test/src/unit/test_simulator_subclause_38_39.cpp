#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

// §38.39 vpi_remove_cb(): removes a simulation-related callback that was
// registered with vpi_register_cb(). Its argument shall be a handle to the
// callback object, it returns 1 on success and 0 on failure, and after a
// successful call the supplied handle is no longer valid. (Registration itself
// is §38.36 machinery, relied on here but not retested.)

namespace delta {
namespace {

int g_38_39_fired = 0;
int CountingCb(VpiCbData*) {
  ++g_38_39_fired;
  return 0;
}

int g_38_39_fired_other = 0;
int OtherCountingCb(VpiCbData*) {
  ++g_38_39_fired_other;
  return 0;
}

class VpiRemoveCbSim : public ::testing::Test {
 protected:
  void SetUp() override {
    g_38_39_fired = 0;
    g_38_39_fired_other = 0;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.39: vpi_remove_cb() shall remove a callback registered with
// vpi_register_cb(), and shall return 1 (true) on success. A removed callback
// is no longer delivered when its reason next occurs.
TEST_F(VpiRemoveCbSim, RemovesRegisteredCallbackAndReturnsOne) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &CountingCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  // While registered, the reason firing delivers the callback.
  ASSERT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 1);
  ASSERT_EQ(g_38_39_fired, 1);

  EXPECT_EQ(vpi_remove_cb(h), 1);

  // After removal the same reason no longer delivers it.
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 0);
  EXPECT_EQ(g_38_39_fired, 1);
}

// §38.39: vpi_remove_cb() removes the specific callback named by its handle.
// With two callbacks registered for the same reason, removing one leaves the
// other registered, so the surviving callback still fires.
TEST_F(VpiRemoveCbSim, RemovesOnlyTheTargetedCallback) {
  s_cb_data cb_a = {};
  cb_a.reason = cbValueChange;
  cb_a.cb_rtn = &CountingCb;
  vpiHandle ha = vpi_register_cb(&cb_a);
  ASSERT_NE(ha, nullptr);

  s_cb_data cb_b = {};
  cb_b.reason = cbValueChange;
  cb_b.cb_rtn = &OtherCountingCb;
  vpiHandle hb = vpi_register_cb(&cb_b);
  ASSERT_NE(hb, nullptr);

  EXPECT_EQ(vpi_remove_cb(ha), 1);

  // Only the survivor (b) is delivered when the reason next occurs.
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbValueChange), 1);
  EXPECT_EQ(g_38_39_fired, 0);
  EXPECT_EQ(g_38_39_fired_other, 1);
}

// §38.39: the argument shall be a handle to the callback object. A handle to a
// different kind of object (here a net) is not a callback object, so removal
// reports failure with 0 (false).
TEST_F(VpiRemoveCbSim, NonCallbackHandleReturnsZero) {
  sim_ctx_.CreateVariable("n", 8);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle net = vpi_handle_by_name("n", nullptr);
  ASSERT_NE(net, nullptr);

  EXPECT_EQ(vpi_remove_cb(net), 0);
}

// §38.39: the routine shall return 0 (false) on failure; a null argument is not
// a handle to a callback object.
TEST_F(VpiRemoveCbSim, NullHandleReturnsZero) {
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);
}

// §38.39: after vpi_remove_cb() is called with a handle to the callback, the
// handle is no longer valid. Reusing the now-stale handle for a second removal
// therefore fails with 0 rather than reporting success again.
TEST_F(VpiRemoveCbSim, HandleIsNoLongerValidAfterRemoval) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  EXPECT_EQ(vpi_remove_cb(h), 1);
  EXPECT_EQ(vpi_remove_cb(h), 0);
}

}  // namespace
}  // namespace delta
