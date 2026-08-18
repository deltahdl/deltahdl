#include "simulator/assoc_element.h"

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

Logic4Vec AssocAllocValue(const AssocArrayObject* aa, Arena& arena) {
  const Logic4Vec* init = nullptr;
  if (aa->has_default) {
    init = &aa->default_value;
  } else if (aa->has_elem_init) {
    init = &aa->elem_init;
  }
  if (init == nullptr)
    return aa->is_4state ? MakeAllX(arena, aa->elem_width)
                         : MakeLogic4VecVal(arena, aa->elem_width, 0);
  // A stored element is as wide as the element type, and a member written into
  // one is deposited at an offset within that width, so an initial value
  // narrower than the element is widened before it becomes the element. A real
  // carries its pattern in a width that says which pattern it is (§6.12), so
  // it is the one value left as it stands.
  if (init->is_real || init->width >= aa->elem_width) return *init;
  return ResizeToWidth(*init, aa->elem_width, arena);
}

// The associative array `sel` selects an element of, or null when its base
// does not name one. A select of anything else — a queue, a fixed-size array,
// a vector — reaches this on the same dispatch and is declined here.
static AssocArrayObject* AssocOfSelect(const Expr* sel, SimContext& ctx) {
  if (!sel || sel->kind != ExprKind::kSelect) return nullptr;
  if (!sel->base || sel->base->kind != ExprKind::kIdentifier) return nullptr;
  if (!sel->index || sel->index_end) return nullptr;
  return ctx.FindAssocArray(sel->base->text);
}

Logic4Vec* AssocEntryForWrite(const Expr* sel, SimContext& ctx, Arena& arena) {
  auto* aa = AssocOfSelect(sel, ctx);
  if (!aa) return nullptr;
  auto idx = EvalExpr(sel->index, ctx, arena);
  if (aa->is_string_key) {
    auto key = AssocStringKey(idx);
    auto it = aa->str_data.find(key);
    if (it == aa->str_data.end())
      it = aa->str_data.emplace(key, AssocAllocValue(aa, arena)).first;
    return &it->second;
  }
  // §7.8.6: an index carrying an x or z bit is invalid, and a write through
  // one is a no-op. Allocating for it would create the entry the invalid write
  // is forbidden to reach.
  if (HasUnknownBits(idx)) return nullptr;
  auto key =
      AssocIntKey(idx, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  auto it = aa->int_data.find(key);
  if (it == aa->int_data.end())
    it = aa->int_data.emplace(key, AssocAllocValue(aa, arena)).first;
  return &it->second;
}

void AllocateAssocEntryForModify(const Expr* lhs, SimContext& ctx,
                                 Arena& arena) {
  AssocEntryForWrite(lhs, ctx, arena);
}

// The dotted member path `expr` names, written the way ResolveStructFieldPath
// reads it: `x` for a single member and `inner.x` for a member of a member.
static void BuildFieldPath(const Expr* expr, std::string& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildFieldPath(expr->lhs, out);
    out += ".";
    BuildFieldPath(expr->rhs, out);
  }
}

// The layout of an associative array's element type, together with the offset
// and width of the member `expr` names within it. `expr` is a member access
// whose left operand selects the element. Returns false unless every part of
// that shape holds and the member resolves.
static bool ResolveAssocMember(const Expr* expr, SimContext& ctx,
                               uint32_t* bit_offset, uint32_t* width) {
  if (!expr || expr->kind != ExprKind::kMemberAccess) return false;
  auto* sel = expr->lhs;
  if (!AssocOfSelect(sel, ctx)) return false;
  const auto* info = ctx.GetVariableStructType(sel->base->text);
  if (!info) return false;
  std::string path;
  BuildFieldPath(expr->rhs, path);
  return ResolveStructFieldPath(info, path, bit_offset, width);
}

bool TryWriteAssocMemberField(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  if (!ResolveAssocMember(lhs, ctx, &bit_offset, &width)) return false;
  auto* entry = AssocEntryForWrite(lhs->lhs, ctx, arena);
  if (!entry) return true;
  DepositBitField(*entry, bit_offset, rhs_val, width);
  return true;
}

bool TryEvalAssocMemberField(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  if (!ResolveAssocMember(expr, ctx, &bit_offset, &width)) return false;
  auto elem = EvalExpr(expr->lhs, ctx, arena);
  out = ExtractBitField(arena, elem, bit_offset, width);
  return true;
}

bool TryWriteAssocElementBits(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
  if (!lhs || lhs->kind != ExprKind::kSelect) return false;
  auto* aa = AssocOfSelect(lhs->base, ctx);
  if (!aa) return false;
  auto* entry = AssocEntryForWrite(lhs->base, ctx, arena);
  if (!entry) return true;
  // WriteBitSelect resolves the index against the declared range of the
  // variable it writes, and an associative array's elements are stored as bare
  // vectors carrying no range. The variable the lowerer creates under the
  // array's name models one element and carries that declaration, so its range
  // is what this element's bits are addressed through.
  Variable elem;
  elem.value = *entry;
  elem.is_4state = aa->is_4state;
  if (auto* decl = ctx.FindVariable(lhs->base->base->text)) {
    elem.is_4state = decl->is_4state;
    elem.is_signed = decl->is_signed;
    elem.packed_elem_width = decl->packed_elem_width;
    elem.has_packed_range = decl->has_packed_range;
    elem.packed_range = decl->packed_range;
  }
  WriteBitSelect(&elem, lhs, rhs_val, ctx, arena);
  *entry = elem.value;
  return true;
}

}  // namespace delta
