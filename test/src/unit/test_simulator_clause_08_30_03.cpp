#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.3: get() returns the referent handle.
TEST(ClassSim, WeakRefGetReturnsReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  EXPECT_EQ(wr.Get(), handle);

  // Verify the referent object is accessible.
  auto* retrieved = f.ctx.GetClassObject(wr.Get());
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved, obj);
}

// §8.30.3: get() returns null after clear.
TEST(ClassSim, WeakRefGetReturnsNullAfterClear) {
  WeakReference wr;
  wr.referent_handle = 42;
  wr.Clear();
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

// §8.30.3: get() on default-constructed returns null.
TEST(ClassSim, WeakRefGetDefaultNull) {
  WeakReference wr;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

}  // namespace
