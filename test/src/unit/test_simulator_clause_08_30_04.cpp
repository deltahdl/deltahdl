#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefClearSetsNull) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  EXPECT_EQ(wr.Get(), handle);

  wr.Clear();
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefClearOnNullSafe) {
  WeakReference wr;
  wr.Clear();
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefClearDoesNotAffectReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 99));

  WeakReference wr;
  wr.referent_handle = handle;
  wr.Clear();

  auto* referent = f.ctx.GetClassObject(handle);
  ASSERT_NE(referent, nullptr);
  EXPECT_EQ(referent->GetProperty("x", f.arena).ToUint64(), 99u);
}

}
