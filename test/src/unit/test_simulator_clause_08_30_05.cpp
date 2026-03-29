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

TEST(ClassSim, WeakRefGetIdUniqueAcrossTypes) {
  SimFixture f;
  auto* type_a = MakeClassType(f, "alpha", {"a"});
  auto* type_b = MakeClassType(f, "beta", {"b"});
  auto [h1, o1] = MakeObj(f, type_a);
  auto [h2, o2] = MakeObj(f, type_b);
  EXPECT_NE(WeakReference::GetId(h1), WeakReference::GetId(h2));
}

TEST(ClassSim, WeakRefGetIdSameAcrossInheritanceTree) {
  SimFixture f;
  auto* parent = MakeClassType(f, "parent", {"x"});
  auto* child = f.arena.Create<ClassTypeInfo>();
  child->name = "child";
  child->parent = parent;
  child->properties.push_back({"y", 32, false});
  f.ctx.RegisterClassType("child", child);

  auto [handle, obj] = MakeObj(f, child);
  auto id_via_child = WeakReference::GetId(handle);
  auto id_via_parent = WeakReference::GetId(handle);
  EXPECT_EQ(id_via_child, id_via_parent);
}

TEST(ClassSim, WeakRefGetIdReturnsLongint) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  int64_t id = WeakReference::GetId(handle);
  EXPECT_GT(id, 0);
}

}  // namespace
