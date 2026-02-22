// §8.20: Virtual methods

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

// AST helper: make an integer literal expression.
static Expr *MkInt(Arena &a, uint64_t val) {
  auto *e = a.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}
// AST helper: make a return statement.
static Stmt *MkReturn(Arena &a, Expr *expr) {
  auto *s = a.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

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
// §8.20: Virtual methods and polymorphism
// =============================================================================
TEST(ClassSim, VirtualMethodDispatch) {
  ClassFixture f;
  auto *base = MakeClassType(f, "Animal", {});
  auto *derived = MakeClassType(f, "Dog", {});
  derived->parent = base;

  auto *base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "speak";
  base_method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 0)));

  auto *derived_method = f.arena.Create<ModuleItem>();
  derived_method->kind = ModuleItemKind::kFunctionDecl;
  derived_method->name = "speak";
  derived_method->func_body_stmts.push_back(
      MkReturn(f.arena, MkInt(f.arena, 1)));

  // Build vtable for base.
  base->vtable.push_back({"speak", base_method, base});
  // Build vtable for derived — overrides speak.
  derived->vtable.push_back({"speak", derived_method, derived});

  auto [handle, obj] = MakeObj(f, derived);
  auto *resolved = obj->ResolveVirtualMethod("speak");
  EXPECT_EQ(resolved, derived_method);
}

TEST(ClassSim, VirtualMethodInheritedNotOverridden) {
  ClassFixture f;
  auto *base = MakeClassType(f, "Base", {});
  auto *derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto *base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "action";

  // Base vtable has action.
  base->vtable.push_back({"action", base_method, base});
  // Derived inherits without override.
  derived->vtable.push_back({"action", base_method, base});

  auto [handle, obj] = MakeObj(f, derived);
  auto *resolved = obj->ResolveVirtualMethod("action");
  EXPECT_EQ(resolved, base_method);
}

// =============================================================================
// Additional integration-style tests
// =============================================================================
TEST(ClassSim, VTableFindIndex) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Foo", {});

  auto *m1 = f.arena.Create<ModuleItem>();
  m1->kind = ModuleItemKind::kFunctionDecl;
  m1->name = "alpha";
  auto *m2 = f.arena.Create<ModuleItem>();
  m2->kind = ModuleItemKind::kFunctionDecl;
  m2->name = "beta";

  type->vtable.push_back({"alpha", m1, type});
  type->vtable.push_back({"beta", m2, type});

  EXPECT_EQ(type->FindVTableIndex("alpha"), 0);
  EXPECT_EQ(type->FindVTableIndex("beta"), 1);
  EXPECT_EQ(type->FindVTableIndex("gamma"), -1);
}

TEST(ClassSim, VirtualMethodNotFound) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto *resolved = obj->ResolveVirtualMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

TEST(ClassSim, EmptyVTable) {
  ClassFixture f;
  auto *type = MakeClassType(f, "NoVirtuals", {});
  EXPECT_TRUE(type->vtable.empty());
  EXPECT_EQ(type->FindVTableIndex("anything"), -1);
}

}  // namespace
