#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3819Test : public ::testing::Test {
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

// §38.19: vpi_handle_by_index

TEST_F(VpiClause3819Test, HandleByIndexReturnCorrectChild) {
  auto *mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  auto *port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);

  vpiHandle result = VpiHandleByIndexC(mod, 1);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, port_b);
}

TEST_F(VpiClause3819Test, HandleByIndexNullParentReturnsNullptr) {
  vpiHandle result = VpiHandleByIndexC(nullptr, 0);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiClause3819Test, HandleByIndexOutOfRangeReturnsNullptr) {
  auto *mod = vpi_ctx_.CreateModule("top", "top");
  vpiHandle result = VpiHandleByIndexC(mod, 99);
  EXPECT_EQ(result, nullptr);
}

}  // namespace
}  // namespace delta
