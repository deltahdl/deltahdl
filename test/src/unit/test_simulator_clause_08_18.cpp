#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, PropertyInfoLocal) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Packet";
  info->properties.push_back({"secret", 32, false, true, false});
  f.ctx.RegisterClassType("Packet", info);

  EXPECT_TRUE(info->properties[0].is_local);
  EXPECT_FALSE(info->properties[0].is_protected);
}

TEST(ClassSim, PropertyInfoProtected) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Packet";
  info->properties.push_back({"hidden", 32, false, false, true});
  f.ctx.RegisterClassType("Packet", info);

  EXPECT_FALSE(info->properties[0].is_local);
  EXPECT_TRUE(info->properties[0].is_protected);
}

TEST(ClassSim, PropertyInfoPublicDefault) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"x"});
  EXPECT_FALSE(type->properties[0].is_local);
  EXPECT_FALSE(type->properties[0].is_protected);
}

TEST(ClassSim, LocalPropertyAccessibleAtRuntime) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Packet";
  info->properties.push_back({"secret", 32, false, true, false});
  f.ctx.RegisterClassType("Packet", info);

  auto* obj = f.arena.Create<ClassObject>();
  obj->type = info;
  obj->properties["secret"] = MakeLogic4VecVal(f.arena, 32, 42);
  EXPECT_EQ(obj->GetProperty("secret", f.arena).ToUint64(), 42u);
}

TEST(ClassSim, ProtectedMemberInherited) {
  SimFixture f;
  auto* base = f.arena.Create<ClassTypeInfo>();
  base->name = "Base";
  base->properties.push_back({"hidden", 32, false, false, true});
  f.ctx.RegisterClassType("Base", base);

  auto* derived = f.arena.Create<ClassTypeInfo>();
  derived->name = "Derived";
  derived->parent = base;
  f.ctx.RegisterClassType("Derived", derived);

  auto* obj = f.arena.Create<ClassObject>();
  obj->type = derived;
  obj->properties["hidden"] = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(obj->GetProperty("hidden", f.arena).ToUint64(), 99u);
}

}  // namespace
