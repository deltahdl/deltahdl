#include "simulator/eval_array_compare.h"

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/dyn_struct_member.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_member_path.h"
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

namespace {

// Whether `layout`, or a structure nested in it, holds a dynamic member.
bool HoldsDynamicMember(const StructTypeInfo& layout) {
  for (const auto& f : layout.fields) {
    if (f.is_dynamic || (f.nested != nullptr && HoldsDynamicMember(*f.nested)))
      return true;
  }
  return false;
}

// Whether `a` and `b` lay out the same members, each variable holding a
// layout of its own.
bool SameLayout(const StructTypeInfo& a, const StructTypeInfo& b) {
  if (a.total_width != b.total_width || a.fields.size() != b.fields.size())
    return false;
  for (size_t i = 0; i < a.fields.size(); ++i) {
    const StructFieldInfo& fa = a.fields[i];
    const StructFieldInfo& fb = b.fields[i];
    if (fa.name != fb.name || fa.bit_offset != fb.bit_offset ||
        fa.width != fb.width || fa.is_dynamic != fb.is_dynamic)
      return false;
  }
  return true;
}

// The elements of the dynamic member `f` at bit `offset` of `value`.
const QueueObject* DynamicElements(const Logic4Vec& value,
                                   const StructFieldInfo& f, uint32_t offset,
                                   Arena& arena) {
  const QueueObject* held =
      DynMemberQueue(ExtractBitField(arena, value, offset, f.width));
  return held != nullptr ? held : DynMemberEmpty(f);
}

// Whether the dynamic members of `layout`, from bit `base` of `a` and `b`,
// hold equal elements; each member's handle is then cleared in both values,
// so that the other members compare as bits.
bool DynamicMembersEqual(const StructTypeInfo& layout, uint32_t base,
                         Logic4Vec& a, Logic4Vec& b, Arena& arena) {
  bool equal = true;
  for (const auto& f : layout.fields) {
    uint32_t offset = base + f.bit_offset;
    if (f.nested != nullptr) {
      equal = DynamicMembersEqual(*f.nested, offset, a, b, arena) && equal;
      continue;
    }
    if (!f.is_dynamic) continue;
    const QueueObject* qa = DynamicElements(a, f, offset, arena);
    const QueueObject* qb = DynamicElements(b, f, offset, arena);
    equal = equal && qa->elements.size() == qb->elements.size();
    for (size_t i = 0; equal && i < qa->elements.size(); ++i)
      equal = SameBits(qa->elements[i], qb->elements[i]);
    Logic4Vec zero = MakeLogic4Vec(arena, f.width);
    DepositBitField(a, offset, zero, f.width);
    DepositBitField(b, offset, zero, f.width);
  }
  return equal;
}

}  // namespace

bool TryDynamicStructEquality(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  bool case_eq =
      expr->op == TokenKind::kEqEqEq || expr->op == TokenKind::kBangEqEq;
  bool logical_eq =
      expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq;
  if ((!case_eq && !logical_eq) || expr->lhs == nullptr ||
      expr->rhs == nullptr) {
    return false;
  }
  const StructTypeInfo* layout = StructLayoutOfOperand(expr->lhs, ctx);
  const StructTypeInfo* other = StructLayoutOfOperand(expr->rhs, ctx);
  if (layout == nullptr || other == nullptr || layout->is_packed ||
      !SameLayout(*layout, *other) || !HoldsDynamicMember(*layout)) {
    return false;
  }
  Logic4Vec a = OwnRhsWords(EvalExpr(expr->lhs, ctx, arena), arena);
  Logic4Vec b = OwnRhsWords(EvalExpr(expr->rhs, ctx, arena), arena);
  bool equal = DynamicMembersEqual(*layout, 0, a, b, arena);
  // §11.4.5: an unknown bit makes == answer x, which the comparison of the
  // values themselves gives; === compares it as it stands.
  if (logical_eq && (!a.IsKnown() || !b.IsKnown())) return false;
  equal = equal && SameBits(a, b);
  bool is_eq = expr->op == TokenKind::kEqEq || expr->op == TokenKind::kEqEqEq;
  out = MakeLogic4VecVal(arena, 1, is_eq == equal ? 1 : 0);
  return true;
}

}  // namespace delta
