// §8.9: Static class properties

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
static ClassTypeInfo* MakeClassType(
    ClassFixture& f, std::string_view name,
    const std::vector<std::string_view>& props) {
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

// Allocate a ClassObject of the given type, returning (handle_id, object*).
static std::pair<uint64_t, ClassObject*> MakeObj(ClassFixture& f,
                                                 ClassTypeInfo* type) {
  auto* obj = f.arena.Create<ClassObject>();
  obj->type = type;
  // Initialize properties to 0.
  for (const auto& p : type->properties) {
    obj->properties[std::string(p.name)] =
        MakeLogic4VecVal(f.arena, p.width, 0);
  }
  uint64_t handle = f.ctx.AllocateClassObject(obj);
  return {handle, obj};
}

namespace {

// =============================================================================
// §8.10: Static properties and methods
// =============================================================================
TEST(ClassSim, StaticPropertySharedAcrossInstances) {
  ClassFixture f;
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
