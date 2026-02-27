// §8.5: Object properties and object parameter data

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
// §8.3-8.5: Property access and assignment
// =============================================================================
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

}  // namespace
