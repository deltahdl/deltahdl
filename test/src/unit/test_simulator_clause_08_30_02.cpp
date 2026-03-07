#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.2: new() with a valid referent stores the handle.
TEST(ClassSim, WeakRefNewWithReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  EXPECT_EQ(wr.Get(), handle);
}

// §8.30.2: new() with null referent — no error, get() returns null.
TEST(ClassSim, WeakRefNewWithNull) {
  WeakReference wr;
  wr.referent_handle = kNullClassHandle;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

// §8.30.2: Each weak_reference instance is unique.
TEST(ClassSim, WeakRefInstancesAreUnique) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr1;
  wr1.referent_handle = handle;
  WeakReference wr2;
  wr2.referent_handle = handle;

  // Same referent, but different WeakReference objects.
  EXPECT_EQ(wr1.Get(), wr2.Get());
  EXPECT_NE(&wr1, &wr2);
}

}  // namespace
