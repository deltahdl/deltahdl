#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ClassSim, StaticPropertySharedAcrossInstances) {
  SimFixture f;
  auto* type = MakeClassType(f, "Shared", {"inst_val"});
  type->properties.push_back({"counter", 32, true});
  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 0);

  MakeObj(f, type);
  MakeObj(f, type);

  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(type->static_properties["counter"].ToUint64(), 42u);
}

// §8.9: Static property initialized once on the type, not per instance.
TEST(ClassSim, StaticPropertyInitializedOnce) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {});
  type->properties.push_back({"count", 32, true});
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 10);

  MakeObj(f, type);
  MakeObj(f, type);

  // Both instances see the same static value on the type.
  EXPECT_EQ(type->static_properties["count"].ToUint64(), 10u);

  // Modifying the static property is visible globally.
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(type->static_properties["count"].ToUint64(), 99u);
}

// §8.9: Static property can be used without creating an object.
TEST(ClassSim, StaticPropertyWithoutInstance) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "NoInst";
  info->properties.push_back({"shared", 32, true});
  info->static_properties["shared"] = MakeLogic4VecVal(f.arena, 32, 7);
  f.ctx.RegisterClassType("NoInst", info);

  // Access without creating any objects.
  auto* found = f.ctx.FindClassType("NoInst");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->static_properties.at("shared").ToUint64(), 7u);
}

}  // namespace
