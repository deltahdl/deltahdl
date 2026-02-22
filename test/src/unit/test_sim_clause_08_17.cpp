// §8.17: Chaining constructors

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
static Expr* MkInt(Arena& a, uint64_t val) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// AST helper: make an identifier expression.
static Expr* MkId(Arena& a, std::string_view name) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// AST helper: make a binary expression.
static Expr* MkBin(Arena& a, TokenKind op, Expr* l, Expr* r) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = l;
  e->rhs = r;
  return e;
}

// AST helper: make a blocking assignment statement.
static Stmt* MkAssign(Arena& a, std::string_view lhs_name, Expr* rhs) {
  auto* s = a.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MkId(a, lhs_name);
  s->rhs = rhs;
  return s;
}

// AST helper: make a return statement.
static Stmt* MkReturn(Arena& a, Expr* expr) {
  auto* s = a.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

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
// §8.15: super.new() chaining
// =============================================================================
TEST(ClassSim, SuperNewChaining) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {"base_val"});
  auto* derived = MakeClassType(f, "Derived", {"child_val"});
  derived->parent = base;

  // Simulate super.new() chain: first init base, then derived.
  auto [handle, obj] = MakeObj(f, derived);

  // Base constructor sets base_val = 10.
  obj->SetProperty("base_val", MakeLogic4VecVal(f.arena, 32, 10));
  // Derived constructor sets child_val = 20.
  obj->SetProperty("child_val", MakeLogic4VecVal(f.arena, 32, 20));

  EXPECT_EQ(obj->GetProperty("base_val", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("child_val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, SuperNewWithArgs) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Vehicle", {"speed"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, {}, "s", nullptr, {}}};
  ctor->func_body_stmts.push_back(
      MkAssign(f.arena, "speed", MkId(f.arena, "s")));
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Car", {"doors"});
  derived->parent = base;

  // Verify base constructor is accessible from derived type chain.
  auto it = derived->parent->methods.find("new");
  ASSERT_NE(it, derived->parent->methods.end());
  auto* base_ctor = it->second;
  ASSERT_NE(base_ctor, nullptr);
  EXPECT_EQ(base_ctor->func_args.size(), 1u);
}

}  // namespace
