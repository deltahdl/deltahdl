// §8.12: Assignment, renaming, and copying

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
struct ClassFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
// Build a simple ClassTypeInfo and register it with the context.
static ClassTypeInfo *MakeClassType(
    ClassFixture &f, std::string_view name,
    const std::vector<std::string_view> &props) {
  auto *info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

// Allocate a ClassObject of the given type, returning (handle_id, object*).
static std::pair<uint64_t, ClassObject *> MakeObj(ClassFixture &f,
                                                  ClassTypeInfo *type) {
  auto *obj = f.arena.Create<ClassObject>();
  obj->type = type;
  // Initialize properties to 0.
  for (const auto &p : type->properties) {
    obj->properties[std::string(p.name)] =
        MakeLogic4VecVal(f.arena, p.width, 0);
  }
  uint64_t handle = f.ctx.AllocateClassObject(obj);
  return {handle, obj};
}

namespace {

// =============================================================================
// §8.12: Object assignment (handle semantics)
// =============================================================================
TEST(ClassSim, HandleAssignmentSharesObject) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Data", {"val"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));

  // Simulate handle copy: both variables hold same handle ID.
  auto *retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 10u);

  // Modify via one handle, visible through the other.
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, HandleNullAssignment) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  // The valid handle works.
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
}

}  // namespace
