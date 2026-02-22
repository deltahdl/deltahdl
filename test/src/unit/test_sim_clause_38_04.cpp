#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3804Test : public ::testing::Test {
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

// §38.4: vpi_control

TEST_F(VpiClause3804Test, ControlFinish) {
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  int result = VpiControlC(vpiFinish, 0);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.FinishRequested());
}

TEST_F(VpiClause3804Test, ControlStop) {
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  int result = VpiControlC(vpiStop, 0);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.StopRequested());
}

TEST_F(VpiClause3804Test, ControlUnknownOpReturnsZero) {
  int result = VpiControlC(999, 0);
  EXPECT_EQ(result, 0);
}

}  // namespace
}  // namespace delta
