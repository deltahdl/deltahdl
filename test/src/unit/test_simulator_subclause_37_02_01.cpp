#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleCreationSim : public ::testing::Test {
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

TEST_F(VpiHandleCreationSim, DistinctHandlesToSameObjectAreEquivalent) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  auto* dup = vpi_ctx_.CreateHandleFor(mod);

  ASSERT_NE(dup, mod);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(mod), VpiHandleOf(dup)), 1);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(dup), VpiHandleOf(mod)), 1);
}

TEST_F(VpiHandleCreationSim, IndependentlyCreatedHandlesAreMutuallyEquivalent) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  auto* dup1 = vpi_ctx_.CreateHandleFor(mod);
  auto* dup2 = vpi_ctx_.CreateHandleFor(dup1);

  ASSERT_NE(dup1, dup2);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(dup1), VpiHandleOf(dup2)), 1);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(dup2), VpiHandleOf(mod)), 1);
}

TEST_F(VpiHandleCreationSim, HandlesForDifferentObjectsAreNotEquivalent) {
  auto* a = vpi_ctx_.CreateModule("a", "a");
  auto* b = vpi_ctx_.CreateModule("b", "b");

  auto* dup_a = vpi_ctx_.CreateHandleFor(a);
  auto* dup_b = vpi_ctx_.CreateHandleFor(b);

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(dup_a), VpiHandleOf(dup_b)), 0);
}

TEST_F(VpiHandleCreationSim, NullObjectYieldsNoHandle) {
  EXPECT_EQ(vpi_ctx_.CreateHandleFor(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
