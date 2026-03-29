#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakReferenceDoesNotPreventGc) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  // Release the only strong reference so the object becomes weakly reachable.
  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  // After GC, the referent should have been reclaimed.
  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, WeakReferenceClearedWhenReferentCollected) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  // Release the strong reference and collect.
  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  // The weak reference should have been cleared by the GC.
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, MultipleWeakRefsClearedAtomically) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr1;
  wr1.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr1);
  WeakReference wr2;
  wr2.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr2);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  // Both weak references to the same referent should be cleared.
  EXPECT_EQ(wr1.Get(), kNullClassHandle);
  EXPECT_EQ(wr2.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakReferenceHasGetIdMethod) {
  EXPECT_EQ(WeakReference::GetId(kNullClassHandle), 0);
  EXPECT_NE(WeakReference::GetId(1), 0);
}

TEST(ClassSim, WeakReferenceInstanceIsGcEligible) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  // Simulate a weak_reference instance as a class object itself.
  auto* wr_type = MakeClassType(f, "weak_reference", {"referent_handle"});
  auto [wr_handle, wr_obj] = MakeObj(f, wr_type);

  // Release the weak_reference instance's strong reference.
  f.ctx.ReleaseObject(wr_handle);
  f.ctx.CollectGarbage();

  // The weak_reference instance should be collected even though the referent
  // is still alive.
  EXPECT_EQ(f.ctx.GetClassObject(wr_handle), nullptr);
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
}

}  // namespace
