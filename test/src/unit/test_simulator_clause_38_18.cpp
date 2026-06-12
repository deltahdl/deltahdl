#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiHandleSim : public ::testing::Test {
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

TEST_F(VpiHandleSim, HandleReturnsParentModule) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port = vpi_ctx_.CreatePort("clk", kVpiInput, mod);

  vpiHandle result = VpiHandleC(vpiModule, port);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, mod);
}

// §38.18: vpi_handle() returns the object of the requested type associated
// with the reference object - here the one-to-one traversal runs in the child
// direction, recovering the port owned by the reference module.
TEST_F(VpiHandleSim, HandleReturnsChildPort) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port = vpi_ctx_.CreatePort("clk", kVpiInput, mod);

  vpiHandle result = VpiHandleC(vpiPort, mod);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, port);
}

TEST_F(VpiHandleSim, HandleReturnsNullptrForNullRef) {
  vpiHandle result = VpiHandleC(vpiModule, nullptr);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleSim, HandleReturnsNullptrForNoMatch) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  vpiHandle result = VpiHandleC(vpiNet, mod);
  EXPECT_EQ(result, nullptr);
}

// §38.18: unless otherwise specified, calling vpi_handle() for a protected
// reference object is an error - no handle is produced and the error status is
// recorded for vpi_chk_error() (§38.2).
TEST_F(VpiHandleSim, HandleProtectedObjectIsAnError) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("clk", kVpiInput, mod);
  mod->is_protected = true;

  vpiHandle result = VpiHandleC(vpiPort, mod);
  EXPECT_EQ(result, nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

}
}
