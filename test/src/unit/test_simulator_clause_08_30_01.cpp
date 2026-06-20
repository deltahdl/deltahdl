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

TEST(ClassSim, WeakReferenceInstanceIsGcEligible) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  auto* wr_type = MakeClassType(f, "weak_reference", {"referent_handle"});
  auto [wr_handle, wr_obj] = MakeObj(f, wr_type);

  f.ctx.ReleaseObject(wr_handle);
  f.ctx.CollectGarbage();

  EXPECT_EQ(f.ctx.GetClassObject(wr_handle), nullptr);
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
}

}  // namespace
