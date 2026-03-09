#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, PropertyInfoConst) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Jumbo";
  info->properties.push_back({"max_size", 32, false, false, false, true});
  f.ctx.RegisterClassType("Jumbo", info);

  EXPECT_TRUE(info->properties[0].is_const);
}

TEST(ClassSim, PropertyInfoNotConstByDefault) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"x"});
  EXPECT_FALSE(type->properties[0].is_const);
}

TEST(ClassSim, GlobalConstantValue) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Config";
  info->properties.push_back({"VERSION", 32, true, false, false, true});
  info->static_properties["VERSION"] = MakeLogic4VecVal(f.arena, 32, 3);
  f.ctx.RegisterClassType("Config", info);

  EXPECT_EQ(info->static_properties["VERSION"].ToUint64(), 3u);
  EXPECT_TRUE(info->properties[0].is_const);
  EXPECT_TRUE(info->properties[0].is_static);
}

TEST(ClassSim, InstanceConstantSetOnObject) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Big_Packet";
  info->properties.push_back({"size", 32, false, false, false, true});
  f.ctx.RegisterClassType("Big_Packet", info);

  auto* obj = f.arena.Create<ClassObject>();
  obj->type = info;
  obj->properties["size"] = MakeLogic4VecVal(f.arena, 32, 4096);

  EXPECT_EQ(obj->GetProperty("size", f.arena).ToUint64(), 4096u);
}

}  // namespace
