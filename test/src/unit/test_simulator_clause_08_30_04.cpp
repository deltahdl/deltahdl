#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.4: clearing a weak reference sets the value returned by get() to null.
// Drive the production allocation path so the reference being cleared is the
// one the runtime manages, not a bare stack struct.
TEST(ClassSim, WeakRefClearSetsGetToNull) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), handle);

  wr->Clear();
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.4: clearing a reference that was initialized with null is safe and
// leaves get() returning null.
TEST(ClassSim, WeakRefClearOnNullInitSafe) {
  SimFixture f;
  auto wr_handle = f.ctx.AllocateWeakReference(kNullClassHandle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);

  wr->Clear();
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.4: clear() only resets the reference; it does not destroy or mutate the
// referent object, which remains reachable through other handles.
TEST(ClassSim, WeakRefClearDoesNotAffectReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 99));

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  wr->Clear();

  auto* referent = f.ctx.GetClassObject(handle);
  ASSERT_NE(referent, nullptr);
  EXPECT_EQ(referent->GetProperty("x", f.arena).ToUint64(), 99u);
}

// §8.30.4: clearing an already-cleared reference keeps get() returning null.
TEST(ClassSim, WeakRefClearIdempotent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);

  wr->Clear();
  EXPECT_EQ(wr->Get(), kNullClassHandle);
  wr->Clear();
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.4: clear() acts on a single reference; another reference to the same
// referent keeps returning that referent from get().
TEST(ClassSim, WeakRefClearDoesNotAffectOtherWeakRefs) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto h1 = f.ctx.AllocateWeakReference(handle, f.arena);
  auto h2 = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr1 = f.ctx.FindWeakReferenceByHandle(h1);
  auto* wr2 = f.ctx.FindWeakReferenceByHandle(h2);
  ASSERT_NE(wr1, nullptr);
  ASSERT_NE(wr2, nullptr);

  wr1->Clear();
  EXPECT_EQ(wr1->Get(), kNullClassHandle);
  EXPECT_EQ(wr2->Get(), handle);
}

}
