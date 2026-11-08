#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {
namespace {

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

TEST_F(VpiHandleValiditySim, FreshHandleIsValid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_TRUE(vpi_ctx_.HandleValid(mod));
}

TEST_F(VpiHandleValiditySim, HandleToVanishedObjectIsInvalid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  ASSERT_TRUE(vpi_ctx_.HandleValid(mod));

  mod->object_exists = false;

  EXPECT_FALSE(vpi_ctx_.HandleValid(mod));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(mod));
}

TEST_F(VpiHandleValiditySim, ReleasingOneHandleLeavesDistinctHandleValid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(other, mod);
  ASSERT_TRUE(vpi_ctx_.HandleValid(other));

  vpi_ctx_.ReleaseHandle(mod);

  EXPECT_FALSE(vpi_ctx_.HandleValid(mod));
  EXPECT_TRUE(vpi_ctx_.HandleValid(other));
}

TEST_F(VpiHandleValiditySim, NullHandleIsInvalid) {
  EXPECT_FALSE(vpi_ctx_.HandleValid(nullptr));
}

TEST_F(VpiHandleValiditySim, HandleAliasingAVanishedObjectIsInvalid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(other, mod);
  ASSERT_TRUE(vpi_ctx_.HandleValid(other));

  mod->object_exists = false;

  EXPECT_FALSE(vpi_ctx_.HandleValid(other));
}

TEST_F(VpiHandleValiditySim, ReleasingAnAliasOfAVanishedObjectFails) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_EQ(vpi_ctx_.ReleaseHandleStatus(other), 1);

  auto* third = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(third, nullptr);
  mod->object_exists = false;

  EXPECT_EQ(vpi_ctx_.ReleaseHandleStatus(third), 0);
  EXPECT_EQ(vpi_ctx_.ReleaseHandleStatus(mod), 0);
}

TEST_F(VpiHandleValiditySim, NoHandleIsCreatedPastAnObjectsLifetime) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(vpi_ctx_.CreateHandleFor(mod), nullptr);

  mod->object_exists = false;

  EXPECT_EQ(vpi_ctx_.CreateHandleFor(mod), nullptr);
}

}  // namespace
}  // namespace delta
