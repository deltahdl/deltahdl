#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3821Test : public ::testing::Test {
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

// §38.21: vpi_handle_by_name

TEST_F(VpiClause3821Test, HandleByNameFindsModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name("dut", nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiType, h), vpiModule);
}

TEST_F(VpiClause3821Test, HandleByNameNullReturnsNullptr) {
  vpiHandle h = vpi_handle_by_name(nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

} // namespace
} // namespace delta
