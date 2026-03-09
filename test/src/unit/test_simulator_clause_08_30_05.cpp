#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefGetIdNull) {
  EXPECT_EQ(WeakReference::GetId(kNullClassHandle), 0);
}

TEST(ClassSim, WeakRefGetIdNonzero) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_NE(WeakReference::GetId(handle), 0);
}

TEST(ClassSim, WeakRefGetIdDeterministic) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  auto id1 = WeakReference::GetId(handle);
  auto id2 = WeakReference::GetId(handle);
  EXPECT_EQ(id1, id2);
}

TEST(ClassSim, WeakRefGetIdUnique) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);
  EXPECT_NE(WeakReference::GetId(h1), WeakReference::GetId(h2));
}

TEST(ClassSim, WeakRefGetIdSameObjectSameId) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(WeakReference::GetId(handle), WeakReference::GetId(handle));
}

}
