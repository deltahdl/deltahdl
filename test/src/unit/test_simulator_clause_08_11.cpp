// §8.11: This

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

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
static ClassTypeInfo *
MakeClassType(ClassFixture &f, std::string_view name,
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
// §8.11: `this` keyword reference
// =============================================================================
TEST(ClassSim, ThisPushPop) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
  f.ctx.PushThis(obj);
  EXPECT_EQ(f.ctx.CurrentThis(), obj);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, NestedThisScoping) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Foo", {"x"});
  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  f.ctx.PushThis(obj1);
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PushThis(obj2);
  EXPECT_EQ(f.ctx.CurrentThis(), obj2);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

} // namespace
