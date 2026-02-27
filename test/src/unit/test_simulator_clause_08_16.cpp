// §8.16: Casting


#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
// Build a simple ClassTypeInfo and register it with the context.
static ClassTypeInfo* MakeClassType(
    SimFixture& f, std::string_view name,
    const std::vector<std::string_view>& props) {
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

namespace {

// =============================================================================
// §8.16: $cast for type checking
// =============================================================================
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

}  // namespace
