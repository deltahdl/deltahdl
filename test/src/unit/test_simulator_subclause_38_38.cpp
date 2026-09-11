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
// The release is observable through HandleReleased, which now reports the
// handle as released where it did not before the call.
TEST_F(VpiReleaseHandleSim, ReleasesAValidHandleAndReportsSuccess) {
  VpiObject obj;
  obj.type = vpiModule;
  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));

  EXPECT_EQ(vpi_release_handle(&obj), 1);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(&obj));
}

// Shall (not called on an invalid handle): once a handle has been released it
// is invalid, so a second vpi_release_handle() on it has no live memory to free
// and fails with 0. The first call succeeds; the repeat reports the failure.
TEST_F(VpiReleaseHandleSim, FailsWhenTheHandleIsAlreadyInvalid) {
  VpiObject obj;
  obj.type = vpiModule;

  EXPECT_EQ(vpi_release_handle(&obj), 1);
  ASSERT_TRUE(vpi_ctx_.HandleReleased(&obj));
  EXPECT_EQ(vpi_release_handle(&obj), 0);
}

// Shall (not called on an invalid handle), null edge: a null handle names no
// object and so is never a valid handle. Passing one leaves nothing to free, so
// the routine fails with 0 rather than acting on it.
TEST_F(VpiReleaseHandleSim, FailsOnANullHandle) {
  EXPECT_EQ(vpi_release_handle(nullptr), 0);
}

// Shall (not called on an invalid handle), destroyed-object edge: a handle
// whose underlying object has ceased to exist is invalid even though the handle
// was never released. The routine has no live object to act on, so it fails
// with 0.
TEST_F(VpiReleaseHandleSim, FailsWhenTheObjectNoLongerExists) {
  VpiObject obj;
  obj.type = vpiModule;
  obj.object_exists = false;

  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));
  EXPECT_EQ(vpi_release_handle(&obj), 0);
}

// Iterator paragraph: vpi_release_handle() may free the memory of an iterator
// object. vpi_scan() reclaims an iterator only once a traversal runs to its
// end; a program that breaks out early - here after a single vpi_scan() -
// releases the iterator instead, and the routine frees that storage and
// returns 1. The iterator is produced by the real vpi_iterate path.
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

// Iterator paragraph, the other half of it: the memory vpi_release_handle()
// frees for an iterator is the iterator's own. §38.38 dates the rest of what
// the traversal touched to somewhere else - "often all required memory has been
// allocated when the underlying object was first created or elaborated" - so
// releasing the iterator leaves the objects it was walking exactly where they
// were, and a fresh iteration over the same scope reaches every one of them
// again.
TEST_F(VpiReleaseHandleSim,
       ReleasingAnIteratorLeavesTheObjectsItWalkedInPlace) {
  VpiObject first_child;
  first_child.type = vpiModule;
  VpiObject second_child;
  second_child.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&first_child, &second_child};

  vpiHandle iter = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(iter, nullptr);
  ASSERT_EQ(vpi_scan(iter), &first_child);
  ASSERT_EQ(vpi_release_handle(iter), 1);

  EXPECT_FALSE(vpi_ctx_.HandleReleased(&first_child));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(&second_child));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(&scope));
  EXPECT_EQ(vpi_get(vpiType, &first_child), vpiModule);

  vpiHandle again = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(again, nullptr);
  EXPECT_EQ(vpi_scan(again), &first_child);
  EXPECT_EQ(vpi_scan(again), &second_child);
  EXPECT_EQ(vpi_scan(again), nullptr);
}

// Iterator paragraph, first sentence: "the iterator object shall automatically
// be freed when vpi_scan() returns NULL because it has ... completed an object
// traversal". A traversal run to its end therefore leaves the application
// nothing to release - which is also what §38.38's advice to release a handle
// excludes, "provided the handle is valid and will not automatically become
// invalid in the future". The iterator here is never released by this test, and
// the storage being gone rather than leaked is what the sanitizer build reads
// back. The scope it walked is untouched, so a second iterator can be built
// over it and this one released the way a broken-out-of loop releases its own.
TEST_F(VpiReleaseHandleSim, AnExhaustedIteratorIsFreedWithoutARelease) {
  VpiObject first_child;
  first_child.type = vpiModule;
  VpiObject second_child;
  second_child.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&first_child, &second_child};

  vpiHandle iter = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_scan(iter), &first_child);
  EXPECT_EQ(vpi_scan(iter), &second_child);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  vpiHandle again = vpi_iterate(vpiModule, &scope);
  ASSERT_NE(again, nullptr);
  EXPECT_EQ(vpi_scan(again), &first_child);
  EXPECT_EQ(vpi_release_handle(again), 1);
}

// §38.38: "One may safely ignore calling vpi_release_handle() when a handle is
// no longer needed, but it is always advisable to do so." The call is advice
// rather than an obligation, so a handle nobody released is still a valid
// handle to its object and still answers for it, and the release it never got
// is one it can still be given later - succeeding then, because the handle was
// valid the whole time.
TEST_F(VpiReleaseHandleSim, AHandleThatIsNeverReleasedStaysValid) {
  VpiObject obj;
  obj.type = vpiModule;

  EXPECT_TRUE(vpi_ctx_.HandleValid(&obj));
  EXPECT_EQ(vpi_get(vpiType, &obj), vpiModule);

  EXPECT_EQ(vpi_release_handle(&obj), 1);
}

}  // namespace
}  // namespace delta
