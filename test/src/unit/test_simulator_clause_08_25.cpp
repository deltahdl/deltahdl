// §8.25: Parameterized classes

#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
// Allocate a ClassObject of the given type, returning (handle_id, object*).

namespace {

// =============================================================================
// §8.25: Parameterized classes (basic cases)
// =============================================================================
TEST(ClassSim, ParameterizedClassDifferentWidths) {
  SimFixture f;

  // Simulate Stack#(8) — 8-bit data property.
  auto* type8 = f.arena.Create<ClassTypeInfo>();
  type8->name = "Stack_8";
  type8->properties.push_back({"data", 8, false});
  f.ctx.RegisterClassType("Stack_8", type8);

  // Simulate Stack#(32) — 32-bit data property.
  auto* type32 = f.arena.Create<ClassTypeInfo>();
  type32->name = "Stack_32";
  type32->properties.push_back({"data", 32, false});
  f.ctx.RegisterClassType("Stack_32", type32);

  auto* t8 = f.ctx.FindClassType("Stack_8");
  auto* t32 = f.ctx.FindClassType("Stack_32");
  ASSERT_NE(t8, nullptr);
  ASSERT_NE(t32, nullptr);
  EXPECT_EQ(t8->properties[0].width, 8u);
  EXPECT_EQ(t32->properties[0].width, 32u);
}

TEST(ClassSim, ParameterizedClassInstantiation) {
  SimFixture f;

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "Pair_int";
  type->properties.push_back({"first", 32, false});
  type->properties.push_back({"second", 32, false});
  f.ctx.RegisterClassType("Pair_int", type);

  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("first", MakeLogic4VecVal(f.arena, 32, 10));
  obj->SetProperty("second", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(obj->GetProperty("first", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("second", f.arena).ToUint64(), 20u);
}

}  // namespace
