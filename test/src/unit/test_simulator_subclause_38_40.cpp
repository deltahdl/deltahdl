#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiScanSim : public ::testing::Test {
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

TEST_F(VpiScanSim, ScanReturnsObjectsDirectedByIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  VpiHandle p0 = vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  VpiHandle p1 = vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(iter, nullptr);

  std::vector<vpiHandle> scanned;
  vpiHandle obj = nullptr;
  while ((obj = vpi_scan(iter)) != nullptr) {
    scanned.push_back(obj);
  }

  ASSERT_EQ(scanned.size(), 2u);
  EXPECT_EQ(VpiObjectOf(scanned[0]), p0);
  EXPECT_EQ(VpiObjectOf(scanned[1]), p1);
}

TEST_F(VpiScanSim, ScanReturnsNullWhenExhausted) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(iter, nullptr);

  EXPECT_NE(vpi_scan(iter), nullptr);
  EXPECT_EQ(vpi_scan(iter), nullptr);
}

TEST_F(VpiScanSim, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

TEST_F(VpiScanSim, FreshIteratorScansIndependently) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle first = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(first, nullptr);
  int first_count = 0;
  while (vpi_scan(first) != nullptr) ++first_count;
  EXPECT_EQ(first_count, 2);

  vpiHandle second = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(second, nullptr);
  int second_count = 0;
  while (vpi_scan(second) != nullptr) ++second_count;
  EXPECT_EQ(second_count, 2);
}

TEST_F(VpiScanSim, ScanRefusesAHandleThatIsNotAnIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  EXPECT_EQ(vpi_scan(VpiHandleOf(mod)), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiScanSim, ARefusedScanLeavesTheObjectInPlace) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  EXPECT_EQ(vpi_scan(VpiHandleOf(mod)), nullptr);
  EXPECT_EQ(vpi_scan(VpiHandleOf(mod)), nullptr);
  EXPECT_EQ(vpi_scan(VpiHandleOf(mod)), nullptr);

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(mod)), vpiModule);
  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);
}

}  // namespace
}  // namespace delta
