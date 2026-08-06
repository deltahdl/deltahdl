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

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(f.ctx.GetClassObject(handle), nullptr);
}

TEST(ClassSim, WeakReferenceClearedWhenReferentCollected) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();

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

  EXPECT_EQ(wr1.Get(), kNullClassHandle);
  EXPECT_EQ(wr2.Get(), kNullClassHandle);
}

// §8.30/§8.29: an instance of the built-in weak_reference class is itself an
// ordinary heap object and is therefore garbage-collection eligible -- once its
// last strong handle is dropped and it becomes unreachable, the collector
// reclaims it. A separate, still strongly reachable object is spared. Per §8.29
// an object is strongly reachable only when a class handle refers to it in an
// active scope (or a pending NBA / the creating process holds it); the
// auxiliary ref count is not part of that definition, so the spared object must
// be rooted in a live variable to be genuinely strongly reachable.
TEST(ClassSim, WeakReferenceInstanceIsGcEligible) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* strong = f.ctx.CreateVariable("strong", 64);
  f.ctx.SetVariableClassType("strong", "obj");
  strong->value = MakeLogic4VecVal(f.arena, 64, handle);

  auto* wr_type = MakeClassType(f, "weak_reference", {"referent_handle"});
  auto [wr_handle, wr_obj] = MakeObj(f, wr_type);

  f.ctx.ReleaseObject(wr_handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(f.ctx.GetClassObject(wr_handle), nullptr);
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
}

}  // namespace
