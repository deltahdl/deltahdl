#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ConstantClassPropertySim, PropertyInfoConst) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Jumbo";
  info->properties.push_back({"max_size", 32, false, false, false, true});
  f.ctx.RegisterClassType("Jumbo", info);

  EXPECT_TRUE(info->properties[0].is_const);
}

TEST(ConstantClassPropertySim, PropertyInfoNotConstByDefault) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"x"});
  EXPECT_FALSE(type->properties[0].is_const);
}

TEST(ConstantClassPropertySim, GlobalConstantValue) {
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

TEST(ConstantClassPropertySim, InstanceConstantSetOnObject) {
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

TEST(ConstantClassPropertySim, GlobalConstantReadBack) {
  EXPECT_EQ(RunAndGet(
      "class Jumbo_Packet;\n"
      "  const int max_size = 9 * 1024;\n"
      "  byte payload [];\n"
      "  function new(int size);\n"
      "    payload = new[size > max_size ? max_size : size];\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Jumbo_Packet p;\n"
      "    p = new(100);\n"
      "    result = p.max_size;\n"
      "  end\n"
      "endmodule\n", "result"), 9u * 1024u);
}

TEST(ConstantClassPropertySim, InstanceConstantAssignedInConstructor) {
  EXPECT_EQ(RunAndGet(
      "class Big_Packet;\n"
      "  const int size;\n"
      "  function new();\n"
      "    size = 4096;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Big_Packet p;\n"
      "    p = new;\n"
      "    result = p.size;\n"
      "  end\n"
      "endmodule\n", "result"), 4096u);
}

TEST(ConstantClassPropertySim, StaticGlobalConstantSharedAcrossInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Config a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    r1 = a.VERSION;\n"
      "    r2 = b.VERSION;\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"r1", 3u}, {"r2", 3u}});
}

TEST(ConstantClassPropertySim, GlobalAndInstanceConstTogether) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Packet;\n"
      "  const int max_size = 1024;\n"
      "  const int size;\n"
      "  function new(int s);\n"
      "    size = s;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r_max, r_size;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new(256);\n"
      "    r_max = p.max_size;\n"
      "    r_size = p.size;\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"r_max", 1024u}, {"r_size", 256u}});
}

TEST(ConstantClassPropertySim, InstanceConstantDifferentPerObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  const int id;\n"
      "  function new(int i);\n"
      "    id = i;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new(10);\n"
      "    b = new(20);\n"
      "    r1 = a.id;\n"
      "    r2 = b.id;\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 20u}});
}

TEST(ConstantClassPropertySim, ConstPropertyInitExprTracked) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Mix";
  // Global constant (has init_expr placeholder).
  info->properties.push_back({"MAX", 32, true, false, false, true});
  // Instance constant (no init_expr).
  ClassTypeInfo::PropertyInfo inst_prop;
  inst_prop.name = "val";
  inst_prop.width = 32;
  inst_prop.is_const = true;
  inst_prop.init_expr = nullptr;
  info->properties.push_back(inst_prop);
  f.ctx.RegisterClassType("Mix", info);

  EXPECT_TRUE(info->properties[0].is_const);
  EXPECT_TRUE(info->properties[0].is_static);
  EXPECT_TRUE(info->properties[1].is_const);
  EXPECT_FALSE(info->properties[1].is_static);
}

}  // namespace
