#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3817Test : public ::testing::Test {
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

// §38.17: vpi_get_vlog_info

TEST_F(VpiClause3817Test, GetVlogInfoReturnsProductAndVersion) {
  SVpiVlogInfo info = {};
  vpi_get_vlog_info(&info);
  ASSERT_NE(info.product, nullptr);
  ASSERT_NE(info.version, nullptr);
  EXPECT_STREQ(info.product, "DeltaHDL");
  EXPECT_STREQ(info.version, "0.1.0");
  EXPECT_EQ(info.argc, 0);
}

TEST_F(VpiClause3817Test, GetVlogInfoNullDoesNotCrash) {
  vpi_get_vlog_info(nullptr);
  // Should not crash.
}

} // namespace
} // namespace delta
