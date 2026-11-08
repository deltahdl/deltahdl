#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

const Expr* UnwrapTypedPattern(const Expr* expr) {
  if (expr->kind == ExprKind::kCast && expr->lhs &&
      expr->lhs->kind == ExprKind::kAssignmentPattern)
    return expr->lhs;
  return expr;
}

const Expr* TypedUnpackedArrayPattern(const Expr* expr, SimContext& ctx) {
  if (expr->kind != ExprKind::kCast || expr->lhs == nullptr ||
      expr->lhs->kind != ExprKind::kAssignmentPattern)
    return nullptr;
  const ModuleItem* item = ctx.FindTypedefItem(expr->text);
  return item != nullptr && !item->unpacked_dims.empty() ? expr->lhs : nullptr;
}

const Expr* UnpackedArrayTypedPattern(const Expr* expr, SimContext& ctx) {
  const Expr* pattern = TypedUnpackedArrayPattern(expr, ctx);
  return pattern != nullptr && pattern->pattern_keys.empty() ? pattern
                                                             : nullptr;
}

bool IsConcatLhs(const Expr* lhs) {
  if (!lhs) return false;
  const Expr* pat = UnwrapTypedPattern(lhs);
  return pat->kind == ExprKind::kConcatenation ||
         pat->kind == ExprKind::kAssignmentPattern;
}

uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx, Arena& arena) {
  if (!lhs) return 0;
  return ConcatLhsElemWidth(lhs, ctx, arena);
}

static const StructTypeInfo* SelectedElementLayout(const Expr* lhs,
                                                   SimContext& ctx) {
  if (lhs->kind == ExprKind::kMemberAccess)
    return ContainerElementLayout(lhs, ctx);
  if (lhs->kind != ExprKind::kSelect || lhs->index_end != nullptr ||
      lhs->base == nullptr || lhs->base->kind != ExprKind::kIdentifier)
    return nullptr;
  std::string_view base = lhs->base->text;
  if (ctx.FindArrayInfo(base) == nullptr && ctx.FindQueue(base) == nullptr)
    return nullptr;
  return StructLayoutOfName(base, ctx);
}

static std::optional<Logic4Vec> PackedVariablePattern(std::string_view name,
                                                      const Expr* pattern,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  const Variable* var = ctx.FindVariable(name);
  if (var == nullptr || !var->has_packed_range ||
      ctx.FindArrayInfo(name) != nullptr || ctx.FindQueue(name) != nullptr)
    return std::nullopt;
  auto span = [](const PackedRange& r) {
    return static_cast<uint32_t>(r.HighIndex() - r.LowIndex() + 1);
  };
  std::vector<uint32_t> spans{span(var->packed_range)};
  for (const PackedRange& dim : var->inner_packed_dims)
    spans.push_back(span(dim));
  return EvalPackedArrayPattern(pattern, spans, var->value.width, ctx, arena);
}

static Logic4Vec EvalRhsForUnstructuredTarget(const Stmt* stmt,
                                              uint32_t ctx_width,
                                              SimContext& ctx, Arena& arena) {
  if (stmt->rhs->kind == ExprKind::kAssignmentPattern) {
    if (auto packed =
            PackedVariablePattern(stmt->lhs->text, stmt->rhs, ctx, arena))
      return *packed;
  }
  return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
}

static bool AnyBitSet(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].aval != 0) return true;
  }
  return false;
}

static bool IsTwoStateIntegerKind(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kByte ||
         kind == DataTypeKind::kShortint || kind == DataTypeKind::kInt ||
         kind == DataTypeKind::kLongint;
}

bool IsRealMemberKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

static std::optional<Logic4Vec> ScalarMemberValue(const Expr* expr,
                                                  const StructTypeInfo& layout,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (layout.is_packed) return std::nullopt;
  const StructFieldInfo* field = FindStructField(&layout, expr->rhs->text);
  if (field == nullptr || field->nested != nullptr || field->elem_count != 0)
    return std::nullopt;
  if (IsRealMemberKind(field->type_kind)) {
    Logic4Vec value = ConvertRealForKnownLhs(EvalExpr(expr->lhs, ctx, arena),
                                             true, field->width, arena);
    value.is_real = false;
    return value;
  }
  if (!IsTwoStateIntegerKind(field->type_kind)) return std::nullopt;
  Logic4Vec value =
      OwnRhsWords(ResizeToWidth(EvalExpr(expr->lhs, ctx, arena, field->width),
                                field->width, arena),
                  arena);
  CoerceTo2State(value);
  return value;
}

std::optional<Logic4Vec> EvalTaggedForLayout(const Expr* expr,
                                             const StructTypeInfo& layout,
                                             SimContext& ctx, Arena& arena) {
  if (expr == nullptr) return std::nullopt;
  if (expr->kind == ExprKind::kTernary) {
    Logic4Vec cond = EvalExpr(expr->condition, ctx, arena);
    if (!cond.IsKnown()) return std::nullopt;
    return EvalTaggedForLayout(
        AnyBitSet(cond) ? expr->true_expr : expr->false_expr, layout, ctx,
        arena);
  }
  if (expr->kind != ExprKind::kTagged || expr->rhs == nullptr ||
      expr->lhs == nullptr)
    return std::nullopt;
  const StructTypeInfo* member = TaggedMemberLayout(layout, expr->rhs->text);
  if (member == nullptr) return ScalarMemberValue(expr, layout, ctx, arena);
  if (expr->lhs->kind == ExprKind::kAssignmentPattern)
    return EvalStructPatternValue(expr->lhs, member, ctx, arena);
  return EvalTaggedForLayout(expr->lhs, *member, ctx, arena);
}

Logic4Vec EvalTaggedOrPlain(const Expr* init, const StructTypeInfo* layout,
                            SimContext& ctx, Arena& arena,
                            uint32_t context_width) {
  if (layout != nullptr) {
    if (auto tagged = EvalTaggedForLayout(init, *layout, ctx, arena))
      return *tagged;
  }
  return EvalExpr(init, ctx, arena, context_width);
}

Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  uint32_t ctx_width = LhsContextWidth(stmt->lhs, ctx, arena);
  if (stmt->rhs != nullptr) {
    const StructTypeInfo* element = SelectedElementLayout(stmt->lhs, ctx);
    const Expr* pattern = UnwrapTypedPattern(stmt->rhs);
    if (element != nullptr && pattern->kind == ExprKind::kAssignmentPattern)
      return EvalStructPatternValue(pattern, element, ctx, arena);
  }
  if (!stmt->rhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  }
  if (const StructTypeInfo* sinfo = StructLayoutOfName(stmt->lhs->text, ctx)) {
    if (auto tagged = EvalTaggedForLayout(stmt->rhs, *sinfo, ctx, arena))
      return *tagged;
  }
  auto* inner = UnwrapTypedPattern(stmt->rhs);
  if (inner->kind != ExprKind::kAssignmentPattern)
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  const StructTypeInfo* sinfo = StructLayoutOfName(stmt->lhs->text, ctx);
  if (!sinfo) sinfo = ContainerElementLayout(stmt->lhs, ctx);
  if (sinfo != nullptr) return EvalStructPatternValue(inner, sinfo, ctx, arena);
  return EvalRhsForUnstructuredTarget(stmt, ctx_width, ctx, arena);
}

uint32_t SelectExprWidth(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena) {
  if (sel->index_end == nullptr) {
    auto level = var.PackedLevelAt(SelectDepthWithin(var, sel, ctx, arena));
    return level ? level->elem_width : 1;
  }
  bool is_indexed = sel->is_part_select_plus || sel->is_part_select_minus;
  auto idx_val = EvalExpr(sel->index, ctx, arena);
  auto end_val = EvalExpr(sel->index_end, ctx, arena);
  if (HasUnknownBits(end_val)) return 0;
  if (!is_indexed && HasUnknownBits(idx_val)) return 0;
  auto target = PartSelectTargetIndices(
      SelectBoundValue(idx_val), SelectBoundValue(end_val),
      sel->is_part_select_plus, sel->is_part_select_minus);
  if (target.declared_width == 0) return 0;
  return static_cast<uint32_t>(std::max(target.first, target.second) -
                               std::min(target.first, target.second) + 1);
}

static bool IndexNamesWholeElement(std::string_view base, SimContext& ctx) {
  return ctx.FindArrayInfo(base) != nullptr || ctx.FindQueue(base) != nullptr ||
         ctx.FindAssocArray(base) != nullptr;
}

uint32_t ConcatLhsElemWidth(const Expr* e, SimContext& ctx, Arena& arena) {
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kAssignmentPattern) {
    uint32_t total = 0;
    for (const auto* sub : e->elements)
      total += ConcatLhsElemWidth(sub, ctx, arena);
    return total;
  }
  auto* var = ResolveLhsVariable(e, ctx);
  if (var == nullptr) {
    if (e->kind != ExprKind::kMemberAccess) return 0;
    const StructFieldInfo* member = ResolveSelectedElementMember(e, ctx).field;
    return member != nullptr ? member->width : FieldLhsWidth(e, ctx);
  }
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      !IndexNamesWholeElement(LhsIdentName(e->base), ctx)) {
    return SelectExprWidth(*var, e, ctx, arena);
  }
  return var->value.width;
}

bool ConcatLhsElemHasWritableBits(const Expr* e, const Variable& var,
                                  SimContext& ctx, Arena& arena) {
  if (e->kind != ExprKind::kSelect || e->base == nullptr) return true;
  return SelectStorageBits(var, e, ctx, arena).width > 0;
}

static void WriteConcatLhsElement(const Expr* el, const Logic4Vec& slice,
                                  SimContext& ctx, Arena& arena) {
  if (auto* elem = TryResolveArrayElement(el, ctx)) {
    WriteVar(elem, slice, arena);
    return;
  }
  if (TryQueueIndexedWrite(el, slice, ctx, arena)) return;
  if (TryAssocIndexedWrite(el, slice, ctx, arena)) return;
  auto* var = ResolveLhsVariable(el, ctx);
  if (var == nullptr) {
    if (el->kind == ExprKind::kMemberAccess) WriteStructField(el, slice, ctx);
    return;
  }
  if (el->kind == ExprKind::kSelect && el->base != nullptr) {
    if (!ConcatLhsElemHasWritableBits(el, *var, ctx, arena)) return;
    WriteBitSelect(var, el, slice, ctx, arena);
    return;
  }
  if (var->is_forced) return;
  var->value = slice;
  var->NotifyWatchers();
}

static void UnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                            SimContext& ctx, Arena& arena) {
  uint32_t bit_offset = 0;
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    const Expr* el = *it;
    uint32_t w = ConcatLhsElemWidth(el, ctx, arena);
    if (w == 0) {
      ReportZeroWidthPartSelect(el, ctx, arena);
      continue;
    }
    Logic4Vec slice = ExtractBitField(arena, rhs_val, bit_offset, w);
    bit_offset += w;
    if (el->kind == ExprKind::kConcatenation ||
        el->kind == ExprKind::kAssignmentPattern) {
      UnpackConcatLhs(el, slice, ctx, arena);
      continue;
    }
    WriteConcatLhsElement(el, slice, ctx, arena);
  }
}

bool TryUnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena) {
  if (!IsConcatLhs(lhs)) return false;
  UnpackConcatLhs(UnwrapTypedPattern(lhs), rhs_val, ctx, arena);
  return true;
}

static void AppendSubarrayLeafNames(const std::string& prefix,
                                    const ArrayInfo& info, size_t d,
                                    std::vector<std::string>& out) {
  uint32_t lo = info.dim_los[d];
  uint32_t size = info.dim_sizes[d];
  bool last = d + 1 == info.dim_sizes.size();
  for (uint32_t i = 0; i < size; ++i) {
    uint32_t addr = info.dim_descending[d] ? lo + size - 1 - i : lo + i;
    std::string child = prefix + "[" + std::to_string(addr) + "]";
    if (last) {
      out.push_back(child);
    } else {
      AppendSubarrayLeafNames(child, info, d + 1, out);
    }
  }
}

size_t StoreSubarrayElements(const SubarrayRef& sub,
                             const std::vector<Logic4Vec>& elems,
                             SimContext& ctx, Arena& arena) {
  std::vector<std::string> leaves;
  AppendSubarrayLeafNames(sub.prefix, sub.info, sub.dim, leaves);
  if (elems.size() != leaves.size()) return leaves.size();
  for (size_t i = 0; i < leaves.size(); ++i) {
    Variable* leaf = ctx.FindVariable(leaves[i]);
    leaf->value =
        OwnRhsWords(ResizeToWidth(elems[i], sub.info.elem_width, arena), arena);
    leaf->NotifyWatchers();
  }
  return leaves.size();
}

bool CopyArrayItemToSubarray(const SubarrayRef& sub, const Expr* item,
                             SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> elems;
  if (!CollectArrayItemElements(item, ctx, arena, elems)) return false;
  if (StoreSubarrayElements(sub, elems, ctx, arena) != elems.size()) {
    ctx.GetDiag().Error(item->range.start,
                        "array size mismatch in assignment to fixed-size array",
                        Subclause("7.6"));
  }
  return true;
}

void DistributeConcatToSubarray(const SubarrayRef& sub, const Expr* concat,
                                SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> elems = CollectConcatElements(concat, ctx, arena);
  size_t count = StoreSubarrayElements(sub, elems, ctx, arena);
  if (elems.size() == count) return;
  ctx.GetDiag().Error(concat->range.start,
                      "unpacked array concatenation size mismatch: expected " +
                          std::to_string(count) + " elements, got " +
                          std::to_string(elems.size()),
                      Subclause("10.10"));
}

}  // namespace delta
