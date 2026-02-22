// §8.5: Object properties and object parameter data

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
// §8.3-8.5: Property access and assignment
// =============================================================================
TEST(ClassSim, PropertySetAndGet) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Packet", {"data"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));
  EXPECT_EQ(obj->GetProperty("data", f.arena).ToUint64(), 42u);
}

TEST(ClassSim, MultipleProperties) {
  ClassFixture f;
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
  ClassFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->GetProperty("nonexistent", f.arena).ToUint64(), 0u);
}

}  // namespace
