#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"

using namespace delta;

// ---------------------------------------------------------------------------
// Expression builders
// ---------------------------------------------------------------------------
inline Expr* MakeInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

inline Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

inline Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

inline Expr* MakeUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
  return e;
}

inline Expr* MakeCall(Arena& arena, std::string_view callee,
                      std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

inline Expr* MakeSysCall(Arena& arena, std::string_view name,
                         std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

inline Expr* MakeSelectExpr(Arena& arena, Expr* base, Expr* index) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

inline Expr* MakeSelect(Arena& arena, std::string_view base, uint64_t idx) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MakeId(arena, base);
  e->index = MakeInt(arena, idx);
  return e;
}

inline Expr* MakeMethodCall(Arena& arena, std::string_view obj,
                            std::string_view method, std::vector<Expr*> args) {
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(arena, obj);
  access->rhs = MakeId(arena, method);

  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = access;
  call->args = std::move(args);
  return call;
}

// ---------------------------------------------------------------------------
// Statement builders
// ---------------------------------------------------------------------------
inline Stmt* MakeAssign(Arena& arena, std::string_view lhs_name, Expr* rhs) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeId(arena, lhs_name);
  s->rhs = rhs;
  return s;
}

inline Stmt* MakeExprStmt(Arena& arena, Expr* expr) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kExprStmt;
  s->expr = expr;
  return s;
}

inline Stmt* MakeReturn(Arena& arena, Expr* expr) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}
