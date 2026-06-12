#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiCompareObjectsSim : public ::testing::Test {
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

// §38.3: vpi_compare_objects() returns TRUE when both handles reference the same
// underlying simulation object. The simplest case: one object, one handle to it
// on both sides.
TEST_F(VpiCompareObjectsSim, SameHandleComparesEqual) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_EQ(VpiCompareObjectsC(mod, mod), 1);
}

// §38.3: distinct objects are not the same object, so the comparison is FALSE.
TEST_F(VpiCompareObjectsSim, DifferentObjectsCompareUnequal) {
  auto* a = vpi_ctx_.CreateModule("a", "a");
  auto* b = vpi_ctx_.CreateModule("b", "b");

  EXPECT_EQ(VpiCompareObjectsC(a, b), 0);
}

// §38.3: object equivalence cannot be determined with a C "==" comparison.
// Example 1 - ps[0] is another way of referring to bit 7 of ps.b, so a handle
// to ps[0] and a handle to ps.b[7] are two different handles that denote the
// same bit. They compare equal even though their pointers differ.
TEST_F(VpiCompareObjectsSim, AliasingHandlesCompareEqualDespiteDistinctPointers) {
  auto* bit = vpi_ctx_.CreateParameter("ps_bit", 0);
  auto* ps_index = vpi_ctx_.CreateParameter("ps_0", 0);    // ps[0]
  auto* member_bit = vpi_ctx_.CreateParameter("ps_b_7", 0);  // ps.b[7]
  ps_index->same_object_as = bit;
  member_bit->same_object_as = bit;

  ASSERT_NE(ps_index, member_bit);  // genuinely different handles
  EXPECT_EQ(VpiCompareObjectsC(ps_index, member_bit), 1);
}

// §38.3, Example 2: obj1 is a handle to the expression i[j] and obj2 is a handle
// to i[0]. The result tracks what i[j] resolves to at the time of the call - TRUE
// when j has the value 0 (i[j] is i[0]) and FALSE when j has the value 1.
TEST_F(VpiCompareObjectsSim, ExpressionHandleTracksResolvedElement) {
  auto* i0 = vpi_ctx_.CreateParameter("i_0", 0);
  auto* i1 = vpi_ctx_.CreateParameter("i_1", 0);
  auto* obj2 = vpi_ctx_.CreateParameter("i_0_iter", 0);
  obj2->same_object_as = i0;  // obj2 derived by iteration refers to i[0]

  // j == 0: i[j] resolves to i[0].
  auto* obj1 = vpi_ctx_.CreateParameter("i_j", 0);
  obj1->same_object_as = i0;
  EXPECT_EQ(VpiCompareObjectsC(obj1, obj2), 1);

  // j == 1: i[j] now resolves to i[1].
  obj1->same_object_as = i1;
  EXPECT_EQ(VpiCompareObjectsC(obj1, obj2), 0);
}

// §38.3, Example 3: obj1 represents c.a and obj2 represents d.a. While both c and
// d are null neither object exists, so the comparison is FALSE - the result holds
// only "provided that the simulation object exists".
TEST_F(VpiCompareObjectsSim, AbsentObjectsCompareUnequal) {
  auto* c_a = vpi_ctx_.CreateParameter("c_a", 0);
  auto* d_a = vpi_ctx_.CreateParameter("d_a", 0);
  c_a->object_exists = false;
  d_a->object_exists = false;

  EXPECT_EQ(VpiCompareObjectsC(c_a, d_a), 0);
}

// §38.3, Example 3 (continued): after c gets a new object, c.a exists but d.a
// does not. A non-existent operand can never compare equal, even when the other
// operand exists.
TEST_F(VpiCompareObjectsSim, OneExistentOneAbsentCompareUnequal) {
  auto* c_a = vpi_ctx_.CreateParameter("c_a", 0);
  auto* d_a = vpi_ctx_.CreateParameter("d_a", 0);
  c_a->object_exists = true;
  d_a->object_exists = false;

  EXPECT_EQ(VpiCompareObjectsC(c_a, d_a), 0);
}

// §38.3: a handle may reach the underlying object through more than one
// intermediate reference (e.g. a select of a select). Both handles must resolve
// all the way to the same underlying object to compare equal, so the comparison
// follows the full chain rather than stopping at the first link.
TEST_F(VpiCompareObjectsSim, TransitiveAliasResolvesToSameObject) {
  auto* underlying = vpi_ctx_.CreateParameter("underlying", 0);
  auto* mid = vpi_ctx_.CreateParameter("mid", 0);
  auto* first = vpi_ctx_.CreateParameter("first", 0);
  auto* second = vpi_ctx_.CreateParameter("second", 0);

  // first -> mid -> underlying; second -> underlying directly.
  mid->same_object_as = underlying;
  first->same_object_as = mid;
  second->same_object_as = underlying;

  EXPECT_EQ(VpiCompareObjectsC(first, second), 1);
}

// §38.3: existence is a property of the underlying object the handle denotes,
// not of the handle. An aliasing handle whose underlying object does not exist
// compares unequal, just as a direct handle to an absent object would.
TEST_F(VpiCompareObjectsSim, AliasToAbsentObjectComparesUnequal) {
  auto* underlying = vpi_ctx_.CreateParameter("underlying", 0);
  underlying->object_exists = false;

  auto* alias_a = vpi_ctx_.CreateParameter("alias_a", 0);
  auto* alias_b = vpi_ctx_.CreateParameter("alias_b", 0);
  // The handles themselves exist, but the object they resolve to does not.
  alias_a->same_object_as = underlying;
  alias_b->same_object_as = underlying;

  EXPECT_EQ(VpiCompareObjectsC(alias_a, alias_b), 0);
}

// §38.3: the routine takes two handles to objects; a null handle names no object
// and therefore never compares equal.
TEST_F(VpiCompareObjectsSim, NullHandleNeverCompareEqual) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_EQ(VpiCompareObjectsC(nullptr, mod), 0);
  EXPECT_EQ(VpiCompareObjectsC(mod, nullptr), 0);
  EXPECT_EQ(VpiCompareObjectsC(nullptr, nullptr), 0);
}

}  // namespace
}  // namespace delta
