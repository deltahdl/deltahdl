#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
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

class HandleEquivalenceInARun : public VpiDesignRun {};

TEST_F(HandleEquivalenceInARun, AScannedAndANamedHandleAreEquivalent) {
  Run("module t;\n"
      "  int v;\n"
      "  int w;\n"
      "endmodule\n");

  vpiHandle by_name = vpi_handle_by_name(VpiText("t.v"), nullptr);
  vpiHandle other = vpi_handle_by_name(VpiText("t.w"), nullptr);
  vpiHandle module = vpi_handle_by_name(VpiText("t"), nullptr);
  vpiHandle scanned = Named(vpiVariables, module, "v");
  ASSERT_NE(by_name, nullptr);
  ASSERT_NE(scanned, nullptr);

  EXPECT_EQ(vpi_compare_objects(scanned, by_name), 1);
  EXPECT_EQ(vpi_compare_objects(by_name, scanned), 1);
  EXPECT_EQ(vpi_compare_objects(scanned, other), 0);
}

TEST_F(HandleEquivalenceInARun, ARelatedAndANamedHandleAreEquivalent) {
  Run("module t;\n"
      "  int v;\n"
      "endmodule\n");

  vpiHandle var = vpi_handle_by_name(VpiText("t.v"), nullptr);
  vpiHandle module = vpi_handle_by_name(VpiText("t"), nullptr);
  ASSERT_NE(var, nullptr);
  vpiHandle related = vpi_handle(vpiModule, var);
  ASSERT_NE(related, nullptr);

  EXPECT_EQ(vpi_compare_objects(related, module), 1);
  EXPECT_EQ(vpi_compare_objects(related, var), 0);
}

}  // namespace
}  // namespace delta
