#pragma once

#include <string_view>

#include "common/arena.h"
#include "parser/ast.h"

using namespace delta;

inline Expr* MkAssocCall(Arena& arena, std::string_view var,
                         std::string_view method, std::string_view ref) {
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
  auto* arg = arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = ref;
  expr->args.push_back(arg);
  return expr;
}
