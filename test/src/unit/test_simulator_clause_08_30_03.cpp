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

TEST(ClassSim, WeakRefGetDefaultNull) {
  WeakReference wr;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefGetReturnsNullAfterGc) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);
  EXPECT_EQ(wr.Get(), handle);

  f.ctx.ReleaseObject(handle);
  f.ctx.CollectGarbage();
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefGetReturnsSameHandleAsInit) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;

  // get() returns the exact value used to initialize (the referent handle).
  EXPECT_EQ(wr.Get(), handle);
  EXPECT_NE(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakRefGetMakesReferentStronglyReachable) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;
  f.ctx.RegisterWeakReference(&wr);

  // Retrieve via get() and store in a strong handle (simulated by looking up
  // the object — the object is still alive because we hold the handle).
  uint64_t strong_handle = wr.Get();
  EXPECT_NE(strong_handle, kNullClassHandle);
  auto* strong_obj = f.ctx.GetClassObject(strong_handle);
  ASSERT_NE(strong_obj, nullptr);
  EXPECT_EQ(strong_obj, obj);
}

TEST(ClassSim, WeakRefGetMultipleCallsConsistent) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  WeakReference wr;
  wr.referent_handle = handle;

  // Multiple calls to get() return the same value.
  EXPECT_EQ(wr.Get(), wr.Get());
  EXPECT_EQ(wr.Get(), handle);
}

TEST(ClassSim, WeakRefGetTakesNoArguments) {
  WeakReference wr;
  // get() is callable with no arguments and returns a handle.
  uint64_t result = wr.Get();
  EXPECT_EQ(result, kNullClassHandle);
}

}  // namespace
