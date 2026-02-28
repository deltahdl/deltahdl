// §8.23: Class scope resolution operator ::

#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "helpers_class_object.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
// Build a simple ClassTypeInfo and register it with the context.

namespace {

// =============================================================================
// §8.23: Class scope resolution operator ::
// =============================================================================
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

}  // namespace
