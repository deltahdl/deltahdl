#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3823Test : public ::testing::Test {
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

// §38.23: vpi_iterate / §38.40: vpi_scan

TEST_F(VpiClause3823Test, IterateModuleChildPorts) {
  auto *mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiClause3823Test, IterateGlobalRegsAfterAttach) {
  sim_ctx_.CreateVariable("v1", 8);
  sim_ctx_.CreateVariable("v2", 16);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle iter = vpi_iterate(vpiReg, nullptr);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiClause3823Test, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
