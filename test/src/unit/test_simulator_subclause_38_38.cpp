#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

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

TEST_F(VpiReleaseHandleSim, ReleasesAValidHandleAndReportsSuccess) {
  VpiObject obj;
  obj.type = vpiModule;
  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));

  EXPECT_EQ(vpi_release_handle(VpiHandleOf(&obj)), 1);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(&obj));
}

TEST_F(VpiReleaseHandleSim, FailsWhenTheHandleIsAlreadyInvalid) {
  VpiObject obj;
  obj.type = vpiModule;

  EXPECT_EQ(vpi_release_handle(VpiHandleOf(&obj)), 1);
  ASSERT_TRUE(vpi_ctx_.HandleReleased(&obj));
  EXPECT_EQ(vpi_release_handle(VpiHandleOf(&obj)), 0);
}

TEST_F(VpiReleaseHandleSim, FailsOnANullHandle) {
  EXPECT_EQ(vpi_release_handle(nullptr), 0);
}

TEST_F(VpiReleaseHandleSim, FailsWhenTheObjectNoLongerExists) {
  VpiObject obj;
  obj.type = vpiModule;
  obj.object_exists = false;

  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));
  EXPECT_EQ(vpi_release_handle(VpiHandleOf(&obj)), 0);
}

TEST_F(VpiReleaseHandleSim, FreesAnIteratorReleasedBeforeExhaustion) {
  VpiObject first_child;
  first_child.type = vpiModule;
  VpiObject second_child;
  second_child.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&first_child, &second_child};

  vpiHandle iter = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(iter, nullptr);

  ASSERT_EQ(VpiObjectOf(vpi_scan(iter)), &first_child);

  EXPECT_EQ(vpi_release_handle(iter), 1);
}

TEST_F(VpiReleaseHandleSim,
       ReleasingAnIteratorLeavesTheObjectsItWalkedInPlace) {
  VpiObject first_child;
  first_child.type = vpiModule;
  VpiObject second_child;
  second_child.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&first_child, &second_child};

  vpiHandle iter = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(iter, nullptr);
  ASSERT_EQ(VpiObjectOf(vpi_scan(iter)), &first_child);
  ASSERT_EQ(vpi_release_handle(iter), 1);

  EXPECT_FALSE(vpi_ctx_.HandleReleased(&first_child));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(&second_child));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(&scope));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&first_child)), vpiModule);

  vpiHandle again = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(again, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(again)), &first_child);
  EXPECT_EQ(VpiObjectOf(vpi_scan(again)), &second_child);
  EXPECT_EQ(vpi_scan(again), nullptr);
}

TEST_F(VpiReleaseHandleSim, AnExhaustedIteratorIsFreedWithoutARelease) {
  VpiObject first_child;
  first_child.type = vpiModule;
  VpiObject second_child;
  second_child.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&first_child, &second_child};

  vpiHandle iter = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &first_child);
  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &second_child);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  vpiHandle again = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(again, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(again)), &first_child);
  EXPECT_EQ(vpi_release_handle(again), 1);
}

TEST_F(VpiReleaseHandleSim, AHandleThatIsNeverReleasedStaysValid) {
  VpiObject obj;
  obj.type = vpiModule;

  EXPECT_TRUE(vpi_ctx_.HandleValid(&obj));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&obj)), vpiModule);

  EXPECT_EQ(vpi_release_handle(VpiHandleOf(&obj)), 1);
}

}  // namespace
}  // namespace delta
