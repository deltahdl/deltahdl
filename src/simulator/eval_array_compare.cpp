#include "simulator/eval_array_compare.h"

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/eval_class_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// The assignment pattern `e` is, typed or untyped, or null.
static const Expr* PatternOperand(const Expr* e) {
  if (e == nullptr) return nullptr;
  const Expr* p = UnwrapTypedPattern(e);
  return p->kind == ExprKind::kAssignmentPattern ? p : nullptr;
}

// The elements of the unpacked array `e` names, from the left: a fixed-size
// one-dimensional array, a queue or dynamic array, or an array property of an
// object. False where `e` names none of them.
static bool ArrayOperandElements(const Expr* e, SimContext& ctx, Arena& arena,
                                 std::vector<Logic4Vec>& out) {
  if (e->kind == ExprKind::kIdentifier) {
    const ArrayInfo* ai = ctx.FindArrayInfo(e->text);
    if (ai != nullptr && !ai->is_dynamic && !ai->is_queue &&
        ai->dim_sizes.empty()) {
      CollectFixedArrayElements(e->text, *ai, ctx, out);
      return true;
    }
    if (const QueueObject* q = ctx.FindQueue(e->text)) {
      out = q->elements;
      return true;
    }
  }
  return PropertyArrayElements(e, ctx, arena, out);
}

// The items of the positional pattern `pattern`, its one replication
// `'{3{2}}` repeated as many times as it says. False for a keyed pattern.
static bool PatternItems(const Expr* pattern, SimContext& ctx, Arena& arena,
                         std::vector<Logic4Vec>& out) {
  if (!pattern->pattern_keys.empty()) return false;
  if (pattern->elements.size() == 1 && pattern->elements[0] != nullptr &&
      pattern->elements[0]->kind == ExprKind::kReplicate) {
    const Expr* rep = pattern->elements[0];
    Logic4Vec count = EvalExpr(rep->repeat_count, ctx, arena);
    if (!count.IsKnown()) return false;
    for (uint64_t k = 0; k < count.ToUint64(); ++k) {
      for (const Expr* item : rep->elements)
        out.push_back(EvalExpr(item, ctx, arena));
    }
    return true;
  }
  for (const Expr* item : pattern->elements)
    out.push_back(EvalExpr(item, ctx, arena));
  return true;
}

// Whether `a` and `b`, of one width, hold the same bits, x and z included.
static bool SameBits(const Logic4Vec& a, const Logic4Vec& b) {
  for (uint32_t w = 0; w < a.nwords && w < b.nwords; ++w) {
    if (a.words[w].aval != b.words[w].aval ||
        a.words[w].bval != b.words[w].bval)
      return false;
  }
  return true;
}

bool TryArrayPatternEquality(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq)
    return false;
  const Expr* pattern = PatternOperand(expr->rhs);
  const Expr* array = expr->lhs;
  if (pattern == nullptr) {
    pattern = PatternOperand(expr->lhs);
    array = expr->rhs;
  }
  if (pattern == nullptr || array == nullptr ||
      PatternOperand(array) != nullptr)
    return false;
  std::vector<Logic4Vec> elems;
  std::vector<Logic4Vec> items;
  if (!ArrayOperandElements(array, ctx, arena, elems)) return false;
  if (!PatternItems(pattern, ctx, arena, items)) return false;
  bool eq = elems.size() == items.size();
  for (size_t i = 0; eq && i < elems.size(); ++i)
    eq = SameBits(elems[i], ResizeToWidth(items[i], elems[i].width, arena));
  out = MakeLogic4VecVal(arena, 1, (expr->op == TokenKind::kEqEq) == eq);
  return true;
}

}  // namespace delta
