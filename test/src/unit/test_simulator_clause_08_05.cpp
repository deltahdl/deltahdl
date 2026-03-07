#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ClassSim, PropertySetAndGet) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"data"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));
  EXPECT_EQ(obj->GetProperty("data", f.arena).ToUint64(), 42u);
}

TEST(ClassSim, MultipleProperties) {
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

TEST(ClassSim, UndefinedPropertyReturnsZero) {
  SimFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->GetProperty("nonexistent", f.arena).ToUint64(), 0u);
}

// §8.5: Class parameters are accessible as properties.
TEST(ClassSim, ParameterAccessAsProperty) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "vector";
  info->properties.push_back({"data", 8, false});
  // §8.5: Parameters registered as properties.
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

// §8.5: Property overwrite preserves latest value.
TEST(ClassSim, PropertyOverwrite) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 10));
  EXPECT_EQ(obj->GetProperty("x", f.arena).ToUint64(), 10u);

  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(obj->GetProperty("x", f.arena).ToUint64(), 20u);
}

}  // namespace
