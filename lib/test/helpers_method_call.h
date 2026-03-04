#pragma once

#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"

using namespace delta;

inline Expr* MakeMethodCallExpr(Arena& arena, std::string_view var_name,
                                std::string_view method_name,
                                std::vector<Expr*> args = {}) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = var_name;

  auto* member = arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = method_name;

  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = id;
  access->rhs = member;

  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = access;
  call->args = std::move(args);
  return call;
}
