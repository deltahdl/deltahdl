// §8.12: Assignment, renaming, and copying

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

// Allocate a ClassObject of the given type, returning (handle_id, object*).

namespace {

// =============================================================================
// §8.12: Object assignment (handle semantics)
// =============================================================================
TEST(ClassSim, HandleAssignmentSharesObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Data", {"val"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));

  // Simulate handle copy: both variables hold same handle ID.
  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 10u);

  // Modify via one handle, visible through the other.
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, HandleNullAssignment) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  // The valid handle works.
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
}

}  // namespace
