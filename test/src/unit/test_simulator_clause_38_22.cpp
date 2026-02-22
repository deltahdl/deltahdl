#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3822Test : public ::testing::Test {
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

// §38.22: vpi_handle_multi

TEST_F(VpiClause3822Test, HandleMultiCombinesChildren) {
  auto *mod1 = vpi_ctx_.CreateModule("m1", "m1");
  vpi_ctx_.CreatePort("p1", kVpiInput, mod1);

  auto *mod2 = vpi_ctx_.CreateModule("m2", "m2");
  vpi_ctx_.CreatePort("p2", kVpiOutput, mod2);

  vpiHandle h = VpiHandleMultiC(vpiPort, mod1, mod2);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(static_cast<int>(h->children.size()), 2);
}

TEST_F(VpiClause3822Test, HandleMultiBothNullReturnsNull) {
  vpiHandle h = VpiHandleMultiC(vpiPort, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

} // namespace
} // namespace delta
