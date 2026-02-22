#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3818Test : public ::testing::Test {
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

// §38.18: vpi_handle

TEST_F(VpiClause3818Test, HandleReturnsParentModule) {
  auto *mod = vpi_ctx_.CreateModule("top", "top");
  auto *port = vpi_ctx_.CreatePort("clk", kVpiInput, mod);

  vpiHandle result = VpiHandleC(vpiModule, port);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, mod);
}

TEST_F(VpiClause3818Test, HandleReturnsNullptrForNullRef) {
  vpiHandle result = VpiHandleC(vpiModule, nullptr);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiClause3818Test, HandleReturnsNullptrForNoMatch) {
  auto *mod = vpi_ctx_.CreateModule("top", "top");
  // Module has no net children, so asking for vpiNet should fail.
  vpiHandle result = VpiHandleC(vpiNet, mod);
  EXPECT_EQ(result, nullptr);
}

} // namespace
} // namespace delta
