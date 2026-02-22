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

class VpiClause3802Test : public ::testing::Test {
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

// §38.2: vpi_chk_error

TEST_F(VpiClause3802Test, ChkErrorNoErrorReturnsZero) {
  SVpiErrorInfo info = {};
  int result = VpiChkErrorC(&info);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(info.level, 0);
}

TEST_F(VpiClause3802Test, ChkErrorNullDoesNotCrash) {
  int result = VpiChkErrorC(nullptr);
  // No error pending, so returns 0.
  EXPECT_EQ(result, 0);
}

}  // namespace
}  // namespace delta
