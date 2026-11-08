#include "simulator/assoc_element.h"

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
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
  if (init->is_real || init->width >= aa->elem_width)
    return OwnRhsWords(*init, arena);
  return ResizeToWidth(*init, aa->elem_width, arena);
}

static AssocArrayObject* AssocOfSelect(const Expr* sel, SimContext& ctx,
                                       Arena& arena,
                                       ClassObject** owner = nullptr) {
  if (!sel || sel->kind != ExprKind::kSelect) return nullptr;
  if (!sel->base || !sel->index || sel->index_end) return nullptr;
  return FindAssocArrayOfBase(sel->base, ctx, arena, owner);
}

static void AnnounceElementChange(const Expr* sel, ClassObject* owner,
                                  SimContext& ctx) {
  if (owner != nullptr) {
    ctx.NotifyClassHandleWatchers(owner->handle);
  } else if (sel->base->kind == ExprKind::kIdentifier) {
    NotifyOwningVar(ctx, sel->base->text);
  }
}

Logic4Vec* AssocEntryForWrite(const Expr* sel, SimContext& ctx, Arena& arena) {
  auto* aa = AssocOfSelect(sel, ctx, arena);
  if (!aa) return nullptr;
  auto idx = EvalExpr(sel->index, ctx, arena);
  if (aa->is_string_key) {
    auto key = AssocStringKey(idx);
    auto it = aa->str_data.find(key);
    if (it == aa->str_data.end())
      it = aa->str_data.emplace(key, AssocAllocValue(aa, arena)).first;
    return &it->second;
  }
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

struct AssocMemberWindow {
  const Expr* select = nullptr;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind kind = DataTypeKind::kImplicit;
};

static const Expr* MemberPathRoot(const Expr* expr, std::string& path) {
  if (expr->kind == ExprKind::kSelect) return expr;
  if (expr->kind != ExprKind::kMemberAccess || expr->lhs == nullptr)
    return nullptr;
  const Expr* root = MemberPathRoot(expr->lhs, path);
  if (root == nullptr) return nullptr;
  if (!path.empty()) path += ".";
  BuildFieldPath(expr->rhs, path);
  return root;
}

static bool ResolveAssocMember(const Expr* expr, SimContext& ctx,
                               AssocMemberWindow& out) {
  if (!expr || expr->kind != ExprKind::kMemberAccess) return false;
  std::string path;
  const Expr* sel = MemberPathRoot(expr, path);
  if (sel == nullptr || !AssocOfSelect(sel, ctx, ctx.GetArena())) return false;
  if (sel->base->kind != ExprKind::kIdentifier) return false;
  const StructTypeInfo* info = StructLayoutOfName(sel->base->text, ctx);
  if (!info) return false;
  out.select = sel;
  return ResolveStructFieldPath(info, path, &out.bit_offset, &out.width,
                                &out.kind);
}

bool TryWriteAssocMemberField(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
  AssocMemberWindow member;
  if (!ResolveAssocMember(lhs, ctx, member)) return false;
  auto* entry = AssocEntryForWrite(member.select, ctx, arena);
  if (!entry) return true;
  DepositBitField(*entry, member.bit_offset,
                  MemberBitsOf(rhs_val, member.kind, arena), member.width);
  NotifyOwningVar(ctx, member.select->base->text);
  return true;
}

bool TryEvalAssocMemberField(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  AssocMemberWindow member;
  if (!ResolveAssocMember(expr, ctx, member)) return false;
  auto elem = EvalExpr(member.select, ctx, arena);
  out = MemberValueOf(
      ExtractBitField(arena, elem, member.bit_offset, member.width),
      member.kind, arena);
  return true;
}

bool TryWriteAssocElementBits(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
  if (!lhs || lhs->kind != ExprKind::kSelect) return false;
  ClassObject* owner = nullptr;
  auto* aa = AssocOfSelect(lhs->base, ctx, arena, &owner);
  if (!aa) return false;
  auto* entry = AssocEntryForWrite(lhs->base, ctx, arena);
  if (!entry) return true;
  Variable elem;
  elem.value = *entry;
  elem.is_4state = aa->is_4state;
  const Variable* decl = nullptr;
  if (owner == nullptr && lhs->base->base->kind == ExprKind::kIdentifier)
    decl = ctx.FindVariable(lhs->base->base->text);
  if (decl != nullptr) {
    elem.is_4state = decl->is_4state;
    elem.is_signed = decl->is_signed;
    elem.packed_elem_width = decl->packed_elem_width;
    elem.has_packed_range = decl->has_packed_range;
    elem.packed_range = decl->packed_range;
  }
  WriteBitSelect(&elem, lhs, rhs_val, ctx, arena);
  *entry = elem.value;
  AnnounceElementChange(lhs->base, owner, ctx);
  return true;
}

}  // namespace delta
