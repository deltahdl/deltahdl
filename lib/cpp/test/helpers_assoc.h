#pragma once

#include <string_view>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "parser/ast.h"

using namespace delta;

// Build aa.method() call expression (no arguments).
inline Expr* MkAssocCallNoArg(Arena& arena, std::string_view var,
                              std::string_view method) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kCall;
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = var;
  auto* meth = arena.Create<Expr>();
  meth->kind = ExprKind::kIdentifier;
  meth->text = method;
  access->lhs = base;
  access->rhs = meth;
  expr->lhs = access;
  return expr;
}

// Build aa.method(ref) call expression.
inline Expr* MkAssocCall(Arena& arena, std::string_view var,
                         std::string_view method, std::string_view ref) {
  auto* expr = MkAssocCallNoArg(arena, var, method);
  auto* arg = arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = ref;
  expr->args.push_back(arg);
  return expr;
}

// Build aa.method(int_literal) call expression.
inline Expr* MkAssocCallInt(Arena& arena, std::string_view var,
                            std::string_view method, int64_t int_arg) {
  auto* expr = MkAssocCallNoArg(arena, var, method);
  auto* arg = arena.Create<Expr>();
  arg->kind = ExprKind::kIntegerLiteral;
  arg->int_val = static_cast<uint64_t>(int_arg);
  expr->args.push_back(arg);
  return expr;
}

// Create assoc array "aa" with entries {10:1, 20:2, 30:3} and ref variable "k".
inline std::pair<AssocArrayObject*, Variable*> MakeAssocWith3Entries(
    SimFixture& f) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 3);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  return {aa, ref};
}
