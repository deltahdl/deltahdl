#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

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

// §38.40: vpi_scan() traverses the hierarchy and returns handles to the objects
// directed by an iterator obtained from vpi_iterate() for a specific object
// type. Each call hands back the next object, in iteration order.
TEST_F(VpiScanSim, ScanReturnsObjectsDirectedByIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpiHandle p0 = vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpiHandle p1 = vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);

  std::vector<vpiHandle> scanned;
  vpiHandle obj = nullptr;
  while ((obj = vpi_scan(iter)) != nullptr) {
    scanned.push_back(obj);
  }

  ASSERT_EQ(scanned.size(), 2u);
  EXPECT_EQ(scanned[0], p0);
  EXPECT_EQ(scanned[1], p1);
}

// §38.40: once the iterator's objects are exhausted vpi_scan() returns NULL.
// That NULL is the point at which the iterator handle is consumed and is no
// longer valid, so the loop must stop using it (this test does not touch the
// handle again after the NULL).
TEST_F(VpiScanSim, ScanReturnsNullWhenExhausted) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);

  EXPECT_NE(vpi_scan(iter), nullptr);  // the single port
  EXPECT_EQ(vpi_scan(iter), nullptr);  // exhausted: NULL ends the scan
}

// §38.40: vpi_scan() on a null iterator handle has nothing to traverse, so it
// reports completion by returning NULL rather than dereferencing the argument.
TEST_F(VpiScanSim, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

// §38.40: a fresh iterator obtained from a new vpi_iterate() call traverses the
// objects independently, so a completed scan does not affect later iterations
// over the same reference object.
TEST_F(VpiScanSim, FreshIteratorScansIndependently) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle first = vpi_iterate(vpiPort, mod);
  ASSERT_NE(first, nullptr);
  int first_count = 0;
  while (vpi_scan(first) != nullptr) ++first_count;
  EXPECT_EQ(first_count, 2);

  vpiHandle second = vpi_iterate(vpiPort, mod);
  ASSERT_NE(second, nullptr);
  int second_count = 0;
  while (vpi_scan(second) != nullptr) ++second_count;
  EXPECT_EQ(second_count, 2);
}

}  // namespace
}  // namespace delta
