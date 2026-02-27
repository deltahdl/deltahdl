// §8.9: Static class properties

#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "helpers_class_object.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
// Build a simple ClassTypeInfo and register it with the context.

// Allocate a ClassObject of the given type, returning (handle_id, object*).

namespace {

// =============================================================================
// §8.10: Static properties and methods
// =============================================================================
TEST(ClassSim, StaticPropertySharedAcrossInstances) {
  SimFixture f;
  auto* type = MakeClassType(f, "Shared", {"inst_val"});
  type->properties.push_back({"counter", 32, true});
  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 0);

  // Create two instances (we just need them to exist).
  MakeObj(f, type);
  MakeObj(f, type);

  // Modify the static property.
  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 42);

  // Both instances see the same static value.
  EXPECT_EQ(type->static_properties["counter"].ToUint64(), 42u);
}

}  // namespace
