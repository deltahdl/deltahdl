// §8.21: Abstract classes and pure virtual methods

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
// §8.21: Abstract classes and pure virtual methods
// =============================================================================
TEST(ClassSim, AbstractClassFlag) {
  ClassFixture f;
  auto *abstract_type = MakeClassType(f, "AbstractBase", {});
  abstract_type->is_abstract = true;

  EXPECT_TRUE(abstract_type->is_abstract);
}

TEST(ClassSim, PureVirtualMethodNullBody) {
  ClassFixture f;
  auto *abstract_type = MakeClassType(f, "Shape", {});
  abstract_type->is_abstract = true;

  // Pure virtual: vtable entry with nullptr method.
  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  EXPECT_EQ(abstract_type->vtable[0].method, nullptr);

  // Concrete derived class overrides it.
  auto *concrete = MakeClassType(f, "Circle", {"radius"});
  concrete->parent = abstract_type;
  auto *method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "area";
  method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 314)));
  concrete->vtable.push_back({"area", method, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  auto *resolved = obj->ResolveVirtualMethod("area");
  EXPECT_EQ(resolved, method);
}

}  // namespace
