#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

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

TEST_F(VpiCallbackSim, RegisterCbAtStartOfSimTime) {
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, cbAtStartOfSimTime);
}

TEST_F(VpiCallbackSim, RemoveCbMarksRemoved) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  int result = VpiRemoveCbC(h);
  EXPECT_EQ(result, 1);

  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].reason, -1);
}

TEST_F(VpiCallbackSim, RemoveCbNullReturnsZero) {
  EXPECT_EQ(VpiRemoveCbC(nullptr), 0);
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
