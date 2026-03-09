#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, IsASameType) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {});
  EXPECT_TRUE(type->IsA(type));
}

TEST(ClassSim, IsADerivedFromBase) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  EXPECT_TRUE(derived->IsA(base));
  EXPECT_FALSE(base->IsA(derived));
}

TEST(ClassSim, IsADeepHierarchy) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {});
  auto* parent = MakeClassType(f, "Parent", {});
  parent->parent = grand;
  auto* child = MakeClassType(f, "Child", {});
  child->parent = parent;

  EXPECT_TRUE(child->IsA(grand));
  EXPECT_TRUE(child->IsA(parent));
  EXPECT_FALSE(grand->IsA(child));
}

TEST(ClassSim, IsAUnrelated) {
  SimFixture f;
  auto* type_a = MakeClassType(f, "A", {});
  auto* type_b = MakeClassType(f, "B", {});

  EXPECT_FALSE(type_a->IsA(type_b));
  EXPECT_FALSE(type_b->IsA(type_a));
}

TEST(ClassSim, CastSubclassToSuperclassAlwaysLegal) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"i"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"j"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_TRUE(obj->type->IsA(base));
}

TEST(ClassSim, CastSuperclassToSubclassIllegal) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, base);
  EXPECT_FALSE(obj->type->IsA(derived));
}

TEST(ClassSim, CastSucceedsWhenObjectIsDerived) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_TRUE(obj->type->IsA(derived));
  EXPECT_TRUE(obj->type->IsA(base));
}

TEST(ClassSim, CastFailsUnrelatedTypes) {
  SimFixture f;
  auto* type_a = MakeClassType(f, "TypeA", {});
  auto* type_b = MakeClassType(f, "TypeB", {});

  auto [handle, obj] = MakeObj(f, type_a);
  EXPECT_FALSE(obj->type->IsA(type_b));
}

TEST(ClassSim, CastNullHandleIsZero) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetClassObject(kNullClassHandle), nullptr);
}

TEST(ClassSim, CastDeepHierarchySucceeds) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = grand;
  auto* leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_TRUE(obj->type->IsA(grand));
  EXPECT_TRUE(obj->type->IsA(mid));

  auto [h2, obj2] = MakeObj(f, grand);
  EXPECT_FALSE(obj2->type->IsA(leaf));
}

}  // namespace
