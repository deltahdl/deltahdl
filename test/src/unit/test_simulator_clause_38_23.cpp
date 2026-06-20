#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiIterateSim : public ::testing::Test {
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

TEST_F(VpiIterateSim, IterateModuleChildPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
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

TEST_F(VpiIterateSim, IterateGlobalRegsAfterAttach) {
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

TEST_F(VpiIterateSim, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

// §38.23: the returned handle is an iterator whose own type is vpiIterator,
// not the type of the objects being traversed.
TEST_F(VpiIterateSim, IteratorHandleTypeIsIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator);
}

// §38.23: vpi_handle(vpiUse, iterator) recovers the reference object the
// iterator was created over.
TEST_F(VpiIterateSim, HandleVpiUseReturnsReferenceObject) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_handle(vpiUse, iter), mod);
}

// §38.23: unless otherwise specified, iterating a protected object is an error,
// so no iterator handle is produced.
TEST_F(VpiIterateSim, IterateProtectedObjectReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  mod->is_protected = true;

  EXPECT_EQ(vpi_iterate(vpiPort, mod), nullptr);
}

// §38.23: when no objects of the requested type are associated with the
// reference handle, vpi_iterate() returns NULL.
TEST_F(VpiIterateSim, IterateNoMatchingObjectsReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  EXPECT_EQ(vpi_iterate(vpiParameter, mod), nullptr);
}

}  // namespace
}  // namespace delta
