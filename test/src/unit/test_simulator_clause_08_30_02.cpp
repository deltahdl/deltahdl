#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.2: new(T referent) records the referent handed to the constructor;
// querying the freshly created weak reference returns that same referent.
TEST(ClassSim, WeakRefNewWithReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), handle);
}

// §8.30.2: a null referent passed to new() is accepted and recorded as null.
TEST(ClassSim, WeakRefNewWithNull) {
  SimFixture f;
  auto wr_handle = f.ctx.AllocateWeakReference(kNullClassHandle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.2: passing null to new() issues no warning.
TEST(ClassSim, WeakRefNewNullNoWarning) {
  SimFixture f;
  f.ctx.AllocateWeakReference(kNullClassHandle, f.arena);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §8.30.2: each weak_reference created by new() is a unique object, so two
// instances built from the same referent have distinct handles even though
// their referents (queried via get()) are equal.
TEST(ClassSim, WeakRefInstancesAreUnique) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr1_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto wr2_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  EXPECT_NE(wr1_handle, wr2_handle);

  auto* wr1 = f.ctx.FindWeakReferenceByHandle(wr1_handle);
  auto* wr2 = f.ctx.FindWeakReferenceByHandle(wr2_handle);
  ASSERT_NE(wr1, nullptr);
  ASSERT_NE(wr2, nullptr);
  EXPECT_NE(wr1, wr2);
  EXPECT_EQ(wr1->Get(), wr2->Get());
}

// §8.30.2 edge case: uniqueness is structural, not referent-derived. Two weak
// references created from a null referent are still distinct objects with
// distinct handles, while both query as null.
TEST(ClassSim, WeakRefNullInstancesAreUnique) {
  SimFixture f;
  auto wr1_handle = f.ctx.AllocateWeakReference(kNullClassHandle, f.arena);
  auto wr2_handle = f.ctx.AllocateWeakReference(kNullClassHandle, f.arena);
  EXPECT_NE(wr1_handle, wr2_handle);

  auto* wr1 = f.ctx.FindWeakReferenceByHandle(wr1_handle);
  auto* wr2 = f.ctx.FindWeakReferenceByHandle(wr2_handle);
  ASSERT_NE(wr1, nullptr);
  ASSERT_NE(wr2, nullptr);
  EXPECT_NE(wr1, wr2);
  EXPECT_EQ(wr1->Get(), kNullClassHandle);
  EXPECT_EQ(wr2->Get(), kNullClassHandle);
}

}
