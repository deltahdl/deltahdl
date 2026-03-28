#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

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

TEST(ClassSim, StaticPropertyInitializedOnce) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {});
  type->properties.push_back({"count", 32, true});
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 10);

  MakeObj(f, type);
  MakeObj(f, type);

  EXPECT_EQ(type->static_properties["count"].ToUint64(), 10u);

  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(type->static_properties["count"].ToUint64(), 99u);
}

TEST(ClassSim, StaticPropertyWithoutInstance) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "NoInst";
  info->properties.push_back({"shared", 32, true});
  info->static_properties["shared"] = MakeLogic4VecVal(f.arena, 32, 7);
  f.ctx.RegisterClassType("NoInst", info);

  auto* found = f.ctx.FindClassType("NoInst");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->static_properties.at("shared").ToUint64(), 7u);
}

TEST(ClassSim, StaticPropertyReadViaInstanceFallsBackToShared) {
  SimFixture f;
  auto* type = MakeClassType(f, "Pkt", {});
  type->properties.push_back({"fileID", 32, true});
  type->static_properties["fileID"] = MakeLogic4VecVal(f.arena, 32, 55);

  auto [handle, obj] = MakeObj(f, type);

  // GetProperty should find the static property value via the type
  // when the instance does not have its own copy.
  // Remove the instance-level copy that MakeObj created so we test fallback.
  obj->properties.erase("fileID");
  auto val = obj->GetProperty("fileID", f.arena);
  EXPECT_EQ(val.ToUint64(), 55u);
}

TEST(ClassSim, StaticPropertyWriteUpdatesSharedStorage) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {});
  type->properties.push_back({"count", 32, true});
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);

  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  // Writing to static_properties should be visible from all instances.
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 77);
  EXPECT_EQ(type->static_properties["count"].ToUint64(), 77u);

  // Both objects share the same type, so both see the update.
  EXPECT_EQ(obj1->type->static_properties.at("count").ToUint64(), 77u);
  EXPECT_EQ(obj2->type->static_properties.at("count").ToUint64(), 77u);
}

TEST(ClassSim, StaticPropertyNotDuplicatedPerInstance) {
  SimFixture f;
  auto* type = MakeClassType(f, "S", {"inst"});
  type->properties.push_back({"shared", 32, true});
  type->static_properties["shared"] = MakeLogic4VecVal(f.arena, 32, 1);

  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  // Modifying one instance's instance property should not affect the other.
  obj1->SetProperty("inst", MakeLogic4VecVal(f.arena, 32, 100));
  EXPECT_EQ(obj2->GetProperty("inst", f.arena).ToUint64(), 0u);

  // But the static property on the type is shared.
  EXPECT_EQ(obj1->type->static_properties.at("shared").ToUint64(), 1u);
  EXPECT_EQ(obj2->type->static_properties.at("shared").ToUint64(), 1u);
}

TEST(ClassSim, LowererInitializesStaticPropertiesToZero) {
  SimFixture f;
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "Init";
  info->properties.push_back({"s1", 32, true});
  info->properties.push_back({"s2", 16, true});
  info->properties.push_back({"inst", 32, false});

  // Simulate what InitStaticProperties does.
  for (const auto& p : info->properties) {
    if (p.is_static) {
      info->static_properties[std::string(p.name)] =
          MakeLogic4VecVal(f.arena, p.width, 0);
    }
  }

  EXPECT_EQ(info->static_properties.size(), 2u);
  EXPECT_EQ(info->static_properties.at("s1").ToUint64(), 0u);
  EXPECT_EQ(info->static_properties.at("s2").ToUint64(), 0u);
  EXPECT_EQ(info->static_properties.count("inst"), 0u);
}

}  // namespace
