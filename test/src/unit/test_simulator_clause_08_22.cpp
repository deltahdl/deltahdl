// §8.22: Polymorphism: dynamic method lookup

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

TEST(ClassSim, PolymorphicVTableMultiLevel) {
  SimFixture f;
  auto* base = MakeClassType(f, "A", {});
  auto* mid = MakeClassType(f, "B", {});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "C", {});
  leaf->parent = mid;

  auto* m_base = f.arena.Create<ModuleItem>();
  m_base->kind = ModuleItemKind::kFunctionDecl;
  m_base->name = "f";
  auto* m_leaf = f.arena.Create<ModuleItem>();
  m_leaf->kind = ModuleItemKind::kFunctionDecl;
  m_leaf->name = "f";

  // A defines f, B inherits, C overrides.
  base->vtable.push_back({"f", m_base, base});
  mid->vtable.push_back({"f", m_base, base});   // Inherited.
  leaf->vtable.push_back({"f", m_leaf, leaf});  // Overridden.

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_EQ(obj->ResolveVirtualMethod("f"), m_leaf);
}

}  // namespace
