#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.3: while the reference has not been cleared, get() returns the referent
// value used to initialize the weak reference. Drive the production allocation
// path so the value queried is the one recorded at construction.
TEST(ClassSim, WeakRefGetReturnsReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), handle);

  auto* retrieved = f.ctx.GetClassObject(wr->Get());
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved, obj);
}

// §8.30.3: a reference initialized with null queries as null.
TEST(ClassSim, WeakRefGetNullReferent) {
  SimFixture f;
  auto wr_handle = f.ctx.AllocateWeakReference(kNullClassHandle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.3: once the reference has been cleared (here by the memory management
// system reclaiming the referent), get() returns null instead of the original
// referent. Drive the production garbage-collection path.
TEST(ClassSim, WeakRefGetReturnsNullAfterGc) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);
  EXPECT_EQ(wr->Get(), handle);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();
  EXPECT_EQ(wr->Get(), kNullClassHandle);
}

// §8.30.3 edge case: when garbage collection runs but the referent is still
// strongly reachable, the reference has not been cleared, so get() keeps
// returning the referent used to initialize it. A live strong handle (a
// class-typed variable holding the object) keeps the referent in the reachable
// set, so the production collector leaves the weak reference intact.
TEST(ClassSim, WeakRefGetReturnsReferentWhenGcSparesReachable) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* strong = f.ctx.CreateVariable("strong", 64);
  f.ctx.SetVariableClassType("strong", "obj");
  strong->value = MakeLogic4VecVal(f.arena, 64, handle);

  auto wr_handle = f.ctx.AllocateWeakReference(handle, f.arena);
  auto* wr = f.ctx.FindWeakReferenceByHandle(wr_handle);
  ASSERT_NE(wr, nullptr);

  f.ctx.CollectGarbage();
  EXPECT_EQ(wr->Get(), handle);
  auto* retrieved = f.ctx.GetClassObject(wr->Get());
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved, obj);
}

}  // namespace
