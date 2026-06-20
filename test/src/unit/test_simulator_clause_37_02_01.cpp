#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.2.1 Handle creation. A tool creates handles as the result of the VPI
// functions a VPI program calls. When asked for a handle to an object it can
// already name, a tool may answer with the same handle or with a new, distinct
// one; two distinct handles that refer to the same object are equivalent. These
// tests observe the simulator's handle-creation path producing such distinct
// but equivalent handles.
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

// §37.2.1: a tool may answer a request for a handle to an existing object with
// a new, distinct handle - a different pointer than the original - and two such
// distinct handles that refer to the same object are equivalent, so
// vpi_compare_objects() reports them equal even though their pointers differ.
TEST_F(VpiHandleCreationSim, DistinctHandlesToSameObjectAreEquivalent) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  auto* dup = vpi_ctx_.CreateHandleFor(mod);

  ASSERT_NE(dup, mod);
  EXPECT_EQ(vpi_compare_objects(mod, dup), 1);
  EXPECT_EQ(vpi_compare_objects(dup, mod), 1);
}

// §37.2.1: equivalence is a property of the underlying object, not of any one
// handle, so two independently created handles to the same object are also
// equivalent to each other - and a handle created from a derived handle still
// resolves to the original object rather than chaining ever deeper.
TEST_F(VpiHandleCreationSim, IndependentlyCreatedHandlesAreMutuallyEquivalent) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  auto* dup1 = vpi_ctx_.CreateHandleFor(mod);
  auto* dup2 = vpi_ctx_.CreateHandleFor(dup1);  // created from a derived handle

  ASSERT_NE(dup1, dup2);
  EXPECT_EQ(vpi_compare_objects(dup1, dup2), 1);
  EXPECT_EQ(vpi_compare_objects(dup2, mod), 1);
}

// §37.2.1: distinct handles are equivalent only when they refer to the *same*
// object. Handles created for different objects are not equivalent.
TEST_F(VpiHandleCreationSim, HandlesForDifferentObjectsAreNotEquivalent) {
  auto* a = vpi_ctx_.CreateModule("a", "a");
  auto* b = vpi_ctx_.CreateModule("b", "b");

  auto* dup_a = vpi_ctx_.CreateHandleFor(a);
  auto* dup_b = vpi_ctx_.CreateHandleFor(b);

  EXPECT_EQ(vpi_compare_objects(dup_a, dup_b), 0);
}

// §37.2.1: a null object denotes nothing, so there is no handle to create.
TEST_F(VpiHandleCreationSim, NullObjectYieldsNoHandle) {
  EXPECT_EQ(vpi_ctx_.CreateHandleFor(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
