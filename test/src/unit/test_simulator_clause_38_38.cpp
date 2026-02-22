#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3838Test : public ::testing::Test {
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

// §38.38: vpi_release_handle (vpi_free_object deprecated per §C.2.4)

TEST_F(VpiClause3838Test, FreeObjectReturnsZero) {
  auto *mod = vpi_ctx_.CreateModule("tmp", "tmp");
  int result = vpi_free_object(mod);
  EXPECT_EQ(result, 0);
}

} // namespace
} // namespace delta
