#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.38 vpi_release_handle(): the public routine that frees the memory a VPI
// routine allocated for a handle and reports 1 (success) or 0 (failure). The
// fixture installs a context so the public C entry runs its real dispatch over
// the test objects.
class VpiReleaseHandleSim : public ::testing::Test {
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

// Shall (free memory) + returns: releasing a valid handle frees it - it stops
// being a live handle to its object - and the routine reports success with 1.
// The release is observable through HandleReleased, which now reports the handle
// as released where it did not before the call.
TEST_F(VpiReleaseHandleSim, ReleasesAValidHandleAndReportsSuccess) {
  VpiObject obj;
  obj.type = vpiModule;
  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));

  EXPECT_EQ(vpi_release_handle(&obj), 1);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(&obj));
}

// Shall (not called on an invalid handle): once a handle has been released it is
// invalid, so a second vpi_release_handle() on it has no live memory to free and
// fails with 0. The first call succeeds; the repeat reports the failure.
TEST_F(VpiReleaseHandleSim, FailsWhenTheHandleIsAlreadyInvalid) {
  VpiObject obj;
  obj.type = vpiModule;

  EXPECT_EQ(vpi_release_handle(&obj), 1);
  ASSERT_TRUE(vpi_ctx_.HandleReleased(&obj));
  EXPECT_EQ(vpi_release_handle(&obj), 0);
}

// Iterator paragraph: vpi_release_handle() may free the memory of an iterator
// object. vpi_scan() reclaims an iterator only once a traversal runs to its end;
// a program that breaks out early - here after a single vpi_scan() - releases
// the iterator instead, and the routine frees that storage and returns 1. The
// iterator is produced by the real vpi_iterate path.
TEST_F(VpiReleaseHandleSim, FreesAnIteratorReleasedBeforeExhaustion) {
  VpiObject first_child;
  first_child.type = vpiModule;
  VpiObject second_child;
  second_child.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&first_child, &second_child};

  vpiHandle iter = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(iter, nullptr);

  // Advance once, then break out of the traversal before it is exhausted.
  ASSERT_EQ(vpi_scan(iter), &first_child);

  EXPECT_EQ(vpi_release_handle(iter), 1);
}

}  // namespace
}  // namespace delta
