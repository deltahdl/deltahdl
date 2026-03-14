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

TEST_F(VpiHandleSim, HandleReturnsNullptrForNullRef) {
  vpiHandle result = VpiHandleC(vpiModule, nullptr);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleSim, HandleReturnsNullptrForNoMatch) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  vpiHandle result = VpiHandleC(vpiNet, mod);
  EXPECT_EQ(result, nullptr);
}

}  // namespace
}  // namespace delta
