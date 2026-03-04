#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

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

  base->vtable.push_back({"f", m_base, base});
  mid->vtable.push_back({"f", m_base, base});
  leaf->vtable.push_back({"f", m_leaf, leaf});

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_EQ(obj->ResolveVirtualMethod("f"), m_leaf);
}

}
