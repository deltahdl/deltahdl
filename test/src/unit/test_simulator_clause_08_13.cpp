// §8.13: Inheritance and subclasses

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

// AST helper: make an identifier expression.
static Expr *MkId(Arena &a, std::string_view name) {
  auto *e = a.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
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
// §8.13: Inheritance with `extends`
// =============================================================================
TEST(ClassSim, InheritanceParentLink) {
  ClassFixture f;
  auto *base = MakeClassType(f, "Base", {"x"});
  auto *derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  EXPECT_EQ(derived->parent, base);
  EXPECT_EQ(derived->parent->name, "Base");
}

TEST(ClassSim, InheritedMethodResolution) {
  ClassFixture f;
  auto *base = MakeClassType(f, "Base", {"x"});

  auto *method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_x";
  method->func_body_stmts.push_back(MkReturn(f.arena, MkId(f.arena, "x")));
  base->methods["get_x"] = method;

  auto *derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  // Should find get_x from base class.
  auto *resolved = obj->ResolveMethod("get_x");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_x");
}

TEST(ClassSim, InheritanceChainPropertyAccess) {
  ClassFixture f;
  auto *grand = MakeClassType(f, "Grand", {"a"});
  auto *parent = MakeClassType(f, "Parent", {"b"});
  parent->parent = grand;
  auto *child = MakeClassType(f, "Child", {"c"});
  child->parent = parent;

  auto [handle, obj] = MakeObj(f, child);
  obj->SetProperty("a", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("b", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("c", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("a", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("b", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("c", f.arena).ToUint64(), 3u);
}

TEST(ClassSim, MethodResolutionWalksChain) {
  ClassFixture f;
  auto *base = MakeClassType(f, "Base", {});
  auto *mid = MakeClassType(f, "Mid", {});
  mid->parent = base;
  auto *leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  // Only base defines the method.
  auto *m = f.arena.Create<ModuleItem>();
  m->kind = ModuleItemKind::kFunctionDecl;
  m->name = "deep_method";
  base->methods["deep_method"] = m;

  auto [handle, obj] = MakeObj(f, leaf);
  auto *resolved = obj->ResolveMethod("deep_method");
  EXPECT_EQ(resolved, m);
}

} // namespace
