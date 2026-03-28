#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ObjectPropertySim, PropertySetAndGet) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"data"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));
  EXPECT_EQ(obj->GetProperty("data", f.arena).ToUint64(), 42u);
}

TEST(ObjectPropertySim, MultipleProperties) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload", "crc"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("header", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("payload", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("crc", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("header", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("payload", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("crc", f.arena).ToUint64(), 3u);
}

TEST(ObjectPropertySim, UndefinedPropertyReturnsZero) {
  SimFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->GetProperty("nonexistent", f.arena).ToUint64(), 0u);
}

TEST(ObjectPropertySim, ParameterAccessAsProperty) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "vector";
  info->properties.push_back({"data", 8, false});

  info->properties.push_back({"width", 32, false});
  f.ctx.RegisterClassType("vector", info);

  auto* obj = f.arena.Create<ClassObject>();
  obj->type = info;
  obj->properties["data"] = MakeLogic4VecVal(f.arena, 8, 0);
  obj->properties["width"] = MakeLogic4VecVal(f.arena, 32, 7);
  uint64_t handle = f.ctx.AllocateClassObject(obj);
  (void)handle;

  EXPECT_EQ(obj->GetProperty("width", f.arena).ToUint64(), 7u);
}

TEST(ObjectPropertySim, PropertyOverwrite) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 10));
  EXPECT_EQ(obj->GetProperty("x", f.arena).ToUint64(), 10u);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(obj->GetProperty("x", f.arena).ToUint64(), 20u);
}

TEST(ObjectPropertySim, PropertyReadViaInstance) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.command = 42;\n"
      "    result = p.command;\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(ObjectPropertySim, MultiplePropertyReadWrite) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
      "  int header;\n"
      "  int payload;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.header = 10;\n"
      "    p.payload = 20;\n"
      "    result = p.header + p.payload;\n"
      "  end\n"
      "endmodule\n", "result"), 30u);
}

TEST(ObjectPropertySim, EnumAccessViaInstance) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
      "  typedef enum integer {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} "
      "PCKT_TYPE;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    result = p.ERR_OVERFLOW;\n"
      "  end\n"
      "endmodule\n", "result"), 10u);
}

TEST(ObjectPropertySim, ParameterValueAccessViaInstance) {
  EXPECT_EQ(RunAndGet(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] data;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    result = v.width;\n"
      "  end\n"
      "endmodule\n", "result"), 3u);
}

TEST(ObjectPropertySim, ParameterDefaultValueAccessViaInstance) {
  EXPECT_EQ(RunAndGet(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] data;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    vector v;\n"
      "    v = new;\n"
      "    result = v.width;\n"
      "  end\n"
      "endmodule\n", "result"), 7u);
}

TEST(ObjectPropertySim, NoRestrictionOnPropertyDataType) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  bit [7:0] b;\n"
      "  logic [15:0] l;\n"
      "  integer ig;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.b = 8'hAB;\n"
      "    c.l = 16'hCDEF;\n"
      "    c.ig = 5;\n"
      "    result = c.ig;\n"
      "  end\n"
      "endmodule\n", "result"), 5u);
}

}  // namespace
