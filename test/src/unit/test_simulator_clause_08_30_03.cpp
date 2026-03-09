#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefGetReturnsReferent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  EXPECT_EQ(wr.Get(), handle);

  auto* retrieved = f.ctx.GetClassObject(wr.Get());
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved, obj);
}

TEST(ClassSim, WeakRefGetReturnsNullAfterClear) {
  WeakReference wr;
  wr.referent_handle = 42;
  wr.Clear();
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefGetDefaultNull) {
  WeakReference wr;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

}  // namespace
