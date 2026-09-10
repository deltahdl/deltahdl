#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.2.4 Validity of handles. A handle is valid from the time of its creation
// until it is released, until the object it refers to ceases to exist, or until
// the tool terminates; at any other time it is invalid. A VPI program is
// required not to refer to an object through an invalid handle, nor to release
// an invalid handle. These tests observe the simulator reporting that validity:
// fresh handles are valid, released handles are not, and a handle to an object
// that has ceased to exist is not.
class VpiHandleValiditySim : public ::testing::Test {
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

// §37.2.4: a handle is valid from the time of its creation. A handle just
// created for a live object is valid.
TEST_F(VpiHandleValiditySim, FreshHandleIsValid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_TRUE(vpi_ctx_.HandleValid(mod));
}

// §37.2.4: validity ends when the object the handle refers to ceases to exist.
// Such a handle is invalid even though it was never released.
TEST_F(VpiHandleValiditySim, HandleToVanishedObjectIsInvalid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  ASSERT_TRUE(vpi_ctx_.HandleValid(mod));

  mod->object_exists = false;  // the object ceases to exist

  EXPECT_FALSE(vpi_ctx_.HandleValid(mod));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(mod));  // not by release - by vanishing
}

// §37.2.4: releasing one handle to an object ends only that handle's validity.
// A distinct, unreleased handle to the same live object stays valid - the
// terminating event that makes a handle invalid is per-handle release, not the
// object disappearing.
TEST_F(VpiHandleValiditySim, ReleasingOneHandleLeavesDistinctHandleValid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);  // a second, distinct handle
  ASSERT_NE(other, mod);
  ASSERT_TRUE(vpi_ctx_.HandleValid(other));

  vpi_ctx_.ReleaseHandle(mod);

  EXPECT_FALSE(vpi_ctx_.HandleValid(mod));
  EXPECT_TRUE(vpi_ctx_.HandleValid(other));
}

// §37.2.4: a null handle refers to nothing and so is never valid.
TEST_F(VpiHandleValiditySim, NullHandleIsInvalid) {
  EXPECT_FALSE(vpi_ctx_.HandleValid(nullptr));
}

// §37.2.4: validity ends when "the object that it refers to ceases to exist",
// and that is the object rather than the handle record. A distinct handle
// aliasing the same object stops being valid when the object goes, even though
// nothing was written on the alias itself.
TEST_F(VpiHandleValiditySim, HandleAliasingAVanishedObjectIsInvalid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(other, mod);
  ASSERT_TRUE(vpi_ctx_.HandleValid(other));

  mod->object_exists = false;  // the object ceases to exist

  EXPECT_FALSE(vpi_ctx_.HandleValid(other));
}

// §37.2.4: "nor shall a VPI program attempt to release an invalid handle", so
// vpi_release_handle() reports failure for the alias of an object that has
// ceased to exist, the same as it does for the handle the object was reached
// through.
TEST_F(VpiHandleValiditySim, ReleasingAnAliasOfAVanishedObjectFails) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_EQ(vpi_ctx_.ReleaseHandleStatus(other), 1);

  auto* third = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(third, nullptr);  // a live object still yields a handle
  mod->object_exists = false;

  EXPECT_EQ(vpi_ctx_.ReleaseHandleStatus(third), 0);
  EXPECT_EQ(vpi_ctx_.ReleaseHandleStatus(mod), 0);
}

// §37.2.4: "A tool can create a handle that refers to an object only during the
// lifetime of the object." Past that lifetime no handle is made, since one made
// then would be invalid from its own creation.
TEST_F(VpiHandleValiditySim, NoHandleIsCreatedPastAnObjectsLifetime) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(vpi_ctx_.CreateHandleFor(mod), nullptr);

  mod->object_exists = false;

  EXPECT_EQ(vpi_ctx_.CreateHandleFor(mod), nullptr);
}

}  // namespace
}  // namespace delta
