#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefNewWithReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  EXPECT_EQ(wr.Get(), handle);
}

TEST(ClassSim, WeakRefNewWithNull) {
  WeakReference wr;
  wr.referent_handle = kNullClassHandle;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefNewNullNoWarning) {
  SimFixture f;
  WeakReference wr;
  wr.referent_handle = kNullClassHandle;
  f.ctx.RegisterWeakReference(&wr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(ClassSim, WeakRefInstancesAreUnique) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr1;
  wr1.referent_handle = handle;
  WeakReference wr2;
  wr2.referent_handle = handle;

  EXPECT_EQ(wr1.Get(), wr2.Get());
  EXPECT_NE(&wr1, &wr2);
}

}  // namespace
