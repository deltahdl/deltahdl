#pragma once

#include <string_view>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "parser/ast.h"

using namespace delta;

// Build a select expression  base_name[int_literal].
inline Expr* MakeAssocSelect(Arena& arena, int64_t idx_val,
                             std::string_view base_name = "aa") {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = idx_val;
  sel->index = idx;
  return sel;
}

// Build a select expression  base_name[string_literal].
inline Expr* MakeAssocSelectStr(Arena& arena, std::string_view base_name,
                                std::string_view key) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kStringLiteral;
  idx->text = key;
  sel->index = idx;
  return sel;
}

// Build a select expression  base_name[ident_name]  (index is an identifier
// reference to another variable rather than a literal).
inline Expr* MakeAssocSelectIdent(Arena& arena, std::string_view base_name,
                                  std::string_view ident_name) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* xref = arena.Create<Expr>();
  xref->kind = ExprKind::kIdentifier;
  xref->text = ident_name;
  sel->index = xref;
  return sel;
}

// Create a variable holding an x/z-tainted index key. The value's low word has
// its b-plane bit set so the key is partially unknown. It is registered as a
// module-scope variable (not a block-local one) so it is resolvable by
// EvalExpr without an active process scope, as these unit tests call the
// assoc-array read/write paths directly.
inline Variable* MakeXTaintedKeyVar(SimFixture& f,
                                    std::string_view name = "__xkey",
                                    uint64_t base_val = 5) {
  auto* var = f.ctx.CreateVariable(name, 32);
  var->value = MakeLogic4VecVal(f.arena, 32, base_val);
  var->value.words[0].bval = 0x1;
  return var;
}

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
