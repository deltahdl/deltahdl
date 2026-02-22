// §8.22: Polymorphism: dynamic method lookup

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

TEST(ClassSim, PolymorphicVTableMultiLevel) {
  ClassFixture f;
  auto *base = MakeClassType(f, "A", {});
  auto *mid = MakeClassType(f, "B", {});
  mid->parent = base;
  auto *leaf = MakeClassType(f, "C", {});
  leaf->parent = mid;

  auto *m_base = f.arena.Create<ModuleItem>();
  m_base->kind = ModuleItemKind::kFunctionDecl;
  m_base->name = "f";
  auto *m_leaf = f.arena.Create<ModuleItem>();
  m_leaf->kind = ModuleItemKind::kFunctionDecl;
  m_leaf->name = "f";

  // A defines f, B inherits, C overrides.
  base->vtable.push_back({"f", m_base, base});
  mid->vtable.push_back({"f", m_base, base});  // Inherited.
  leaf->vtable.push_back({"f", m_leaf, leaf}); // Overridden.

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_EQ(obj->ResolveVirtualMethod("f"), m_leaf);
}

} // namespace
