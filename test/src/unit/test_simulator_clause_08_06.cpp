#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MkBin(Arena& a, TokenKind op, Expr* l, Expr* r) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = l;
  e->rhs = r;
  return e;
}

namespace {

TEST(ClassSim, SimpleMethodCall) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {"count"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_count";
  method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkId(f.arena, "count")));
  type->methods["get_count"] = method;

  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("count", MakeLogic4VecVal(f.arena, 32, 99));

  auto* resolved = obj->ResolveMethod("get_count");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_count");
}

TEST(ClassSim, MethodWithArgs) {
  SimFixture f;
  auto* type = MakeClassType(f, "Adder", {"total"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "add";
  method->return_type.kind = DataTypeKind::kVoid;
  method->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  auto* rhs = MkBin(f.arena, TokenKind::kPlus, MkId(f.arena, "total"),
                    MkId(f.arena, "v"));
  method->func_body_stmts.push_back(MakeAssign(f.arena, "total", rhs));
  type->methods["add"] = method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("add");
  EXPECT_NE(resolved, nullptr);
}

TEST(ClassSim, MethodNotFound) {
  SimFixture f;
  auto* type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto* resolved = obj->ResolveMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

}
