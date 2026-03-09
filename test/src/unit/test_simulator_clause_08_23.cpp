#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, ScopeResolutionStaticLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {});
  type->static_properties["MAX_SIZE"] = MakeLogic4VecVal(f.arena, 32, 256);

  auto it = type->static_properties.find("MAX_SIZE");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 256u);
}

TEST(ClassSim, ScopeResolutionMethodLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Utils", {});
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "compute";
  method->is_static = true;
  type->methods["compute"] = method;

  auto* found = f.ctx.FindClassType("Utils");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("compute");
  ASSERT_NE(it, found->methods.end());
  EXPECT_EQ(it->second->name, "compute");
}

TEST(ClassSim, ScopeResolutionMultipleStaticProps) {
  SimFixture f;
  auto* type = MakeClassType(f, "Config", {});
  type->static_properties["WIDTH"] = MakeLogic4VecVal(f.arena, 32, 8);
  type->static_properties["DEPTH"] = MakeLogic4VecVal(f.arena, 32, 16);

  EXPECT_EQ(type->static_properties["WIDTH"].ToUint64(), 8u);
  EXPECT_EQ(type->static_properties["DEPTH"].ToUint64(), 16u);
}

TEST(ClassSim, ScopeResolutionMissingProperty) {
  SimFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto it = type->static_properties.find("nonexistent");
  EXPECT_EQ(it, type->static_properties.end());
}

TEST(ClassSim, ScopeResolutionDisambiguates) {
  SimFixture f;
  auto* type = MakeClassType(f, "Base", {});
  type->static_properties["bin"] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* local = f.ctx.CreateLocalVariable("bin", 32);
  local->value = MakeLogic4VecVal(f.arena, 32, 123);

  auto it = type->static_properties.find("bin");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 42u);
  EXPECT_EQ(local->value.ToUint64(), 123u);
}

TEST(ClassSim, ScopeResolutionBaseClassStatic) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  base->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 7);

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* found = f.ctx.FindClassType("Base");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->static_properties["count"].ToUint64(), 7u);
}

}
