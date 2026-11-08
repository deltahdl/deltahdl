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
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

void WritePartSelect(Variable* var, const PartSelectBits& bits,
                     const Logic4Vec& rhs_val, Arena& arena) {
  Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
  DepositBitField(updated, bits.lo,
                  ExtractBitField(arena, rhs_val, bits.src_lo, bits.width),
                  bits.width);
  var->value = updated;
  if (!var->is_4state) CoerceTo2State(var->value);
}

struct SelectAddressing {
  PackedRange bits;
  PackedRange elems;
  uint32_t elem_width;

  static SelectAddressing OfVariable(const Variable& var) {
    return {var.BitSelectRange(), var.DeclaredRange(), var.packed_elem_width};
  }
  static SelectAddressing OfWindow(const Variable& var, size_t depth,
                                   uint32_t width) {
    PackedRange flat = PackedRange::Implicit(width);
    auto level = var.PackedLevelWithin(depth, width);
    if (!level) return {flat, flat, 0};
    return {level->elem_width > 1 ? flat : level->range, level->range,
            level->elem_width};
  }
};

static PartSelectBits ResolveSelectBits(const SelectAddressing& at,
                                        const Expr* sel, SimContext& ctx,
                                        Arena& arena) {
  auto idx_val = EvalExpr(sel->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return {0, 0};
  auto idx = SelectBoundValue(idx_val);
  if (sel->index_end == nullptr) {
    if (at.elem_width > 1) {
      if (!at.elems.Contains(idx)) return {0, 0};
      auto base = static_cast<uint32_t>(at.elems.OffsetOf(idx));
      return {base * at.elem_width, at.elem_width};
    }
    if (!at.bits.Contains(idx)) return {0, 0};
    return {static_cast<uint32_t>(at.bits.OffsetOf(idx)), 1};
  }
  auto end_val = EvalExpr(sel->index_end, ctx, arena);
  if (HasUnknownBits(end_val)) return {0, 0};
  auto target = PartSelectTargetIndices(idx, SelectBoundValue(end_val),
                                        sel->is_part_select_plus,
                                        sel->is_part_select_minus);
  if (target.declared_width == 0) return {0, 0};
  if (at.elem_width > 1) {
    PartSelectBits elems =
        PartSelectStorageBits(at.elems, target.first, target.second);
    return {elems.lo * at.elem_width, elems.width * at.elem_width,
            elems.src_lo * at.elem_width};
  }
  return PartSelectStorageBits(at.bits, target.first, target.second);
}

size_t SelectDepthWithin(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena) {
  const Expr* base = sel->base;
  if (base == nullptr || base->kind != ExprKind::kSelect) return 0;
  size_t depth = 0;
  for (const Expr* p = base; p != nullptr; p = p->base, ++depth) {
    std::string name;
    if (!BuildCompoundLhsName(p, ctx, arena, name)) {
      if (p->kind != ExprKind::kSelect) break;
      continue;
    }
    const Variable* named = ctx.FindVariable(name);
    if (named == nullptr) continue;
    return named == &var ? depth : 0;
  }
  return 0;
}

PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena) {
  size_t depth = SelectDepthWithin(var, sel, ctx, arena);
  if (depth == 0) {
    return ResolveSelectBits(SelectAddressing::OfVariable(var), sel, ctx,
                             arena);
  }
  PartSelectBits inner = SelectStorageBits(var, sel->base, ctx, arena);
  if (inner.width == 0) return {0, 0};
  PartSelectBits within = ResolveSelectBits(
      SelectAddressing::OfWindow(var, depth, inner.width), sel, ctx, arena);
  if (within.width == 0) return {0, 0};
  return {inner.lo + within.lo, within.width, within.src_lo};
}

static bool StoredBitsDiffer(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return true;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return true;
  }
  return false;
}

void ReportZeroWidthPartSelect(const Expr* sel, SimContext& ctx, Arena& arena) {
  if (!sel->index_end) return;
  if (!sel->is_part_select_plus && !sel->is_part_select_minus) return;
  auto width = SelectBoundValue(EvalExpr(sel->index_end, ctx, arena));
  auto target = PartSelectTargetIndices(0, width, sel->is_part_select_plus,
                                        sel->is_part_select_minus);
  if (target.declared_width != 0) return;
  ctx.GetDiag().Error(sel->range.start, "zero-width part-select is not allowed",
                      Subclause("11.5.1"));
}

static void WriteBitSelectBits(Variable* var, const Expr* lhs,
                               const Logic4Vec& rhs_val, SimContext& ctx,
                               Arena& arena) {
  ReportZeroWidthPartSelect(lhs, ctx, arena);
  PartSelectBits bits = SelectStorageBits(*var, lhs, ctx, arena);
  if (bits.width == 0) return;
  WritePartSelect(var, bits, rhs_val, arena);
}

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  if (var->is_forced) return;
  Logic4Snapshot before;
  before.Capture(var->value);
  WriteBitSelectBits(var, lhs, rhs_val, ctx, arena);
  if (StoredBitsDiffer(before.Get(), var->value)) var->NotifyWatchers();
}

static Logic4Vec ResizeNarrowKnown(const Logic4Vec& val, uint32_t target_width,
                                   Arena& arena) {
  uint64_t v = val.ToUint64();
  if (val.is_signed && target_width > val.width && val.width > 0 &&
      val.width < 64) {
    uint64_t sign_bit = uint64_t{1} << (val.width - 1);
    if (v & sign_bit) v |= ~uint64_t{0} << val.width;
  }
  Logic4Vec result = MakeLogic4VecVal(arena, target_width, v);
  result.is_signed = val.is_signed;
  return result;
}

static void SignExtendWideResult(const Logic4Vec& val, uint32_t target_width,
                                 Logic4Vec& result) {
  if (!val.is_signed || target_width <= val.width || val.width == 0) return;
  uint32_t msb_idx = (val.width - 1) / 64;
  uint64_t msb_mask = uint64_t{1} << ((val.width - 1) % 64);
  uint64_t a_fill = (val.words[msb_idx].aval & msb_mask) ? ~uint64_t{0} : 0;
  uint64_t b_fill = (val.words[msb_idx].bval & msb_mask) ? ~uint64_t{0} : 0;
  if (!(a_fill || b_fill)) return;
  uint32_t fill_bit = val.width % 64;
  if (fill_bit != 0) {
    uint64_t fill_mask = ~((uint64_t{1} << fill_bit) - 1);
    uint32_t target_bits_in_word = target_width % 64;
    if (target_bits_in_word > fill_bit) {
      uint64_t upper_limit = (uint64_t{1} << target_bits_in_word) - 1;
      fill_mask &= upper_limit;
    }
    result.words[val.width / 64].aval |= a_fill & fill_mask;
    result.words[val.width / 64].bval |= b_fill & fill_mask;
  }
  uint32_t first_full = val.width / 64 + (fill_bit != 0 ? 1 : 0);
  for (uint32_t i = first_full; i < result.nwords; ++i) {
    result.words[i].aval = a_fill;
    result.words[i].bval = b_fill;
  }
}

static void MaskHighBits(uint32_t target_width, Logic4Vec& result) {
  uint32_t last_bit = target_width % 64;
  if (last_bit == 0) return;
  uint32_t last_word = (target_width - 1) / 64;
  uint64_t mask = (uint64_t{1} << last_bit) - 1;
  result.words[last_word].aval &= mask;
  result.words[last_word].bval &= mask;
}

Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena) {
  if (val.fills_width && target_width > val.width)
    return FillUnbasedUnsized(val, target_width, arena);
  val.fills_width = false;
  if (val.width == target_width || target_width == 0) return val;

  bool has_xz = false;
  for (uint32_t i = 0; i < val.nwords && !has_xz; ++i)
    has_xz = val.words[i].bval != 0;

  if (!has_xz && val.width <= 64 && target_width <= 64)
    return ResizeNarrowKnown(val, target_width, arena);

  auto result = MakeLogic4Vec(arena, target_width);
  result.is_signed = val.is_signed;
  uint32_t copy_words = std::min(val.nwords, result.nwords);
  for (uint32_t i = 0; i < copy_words; ++i) {
    result.words[i].aval = val.words[i].aval;
    result.words[i].bval = val.words[i].bval;
  }
  SignExtendWideResult(val, target_width, result);
  MaskHighBits(target_width, result);
  return result;
}

Logic4Vec SizedForQueueElement(const QueueObject& q, Logic4Vec val,
                               Arena& arena) {
  if (val.is_string || val.is_real || q.holds_class_handles) return val;
  return ResizeToWidth(val, q.elem_width, arena);
}

void SizeAndOwnQueueElements(const QueueObject& q,
                             std::vector<Logic4Vec>& elems, Arena& arena) {
  for (Logic4Vec& elem : elems)
    elem = OwnRhsWords(SizedForQueueElement(q, elem, arena), arena);
}

static void AppendLeafSuffixes(const ArrayInfo& info, size_t d,
                               const std::string& prefix,
                               std::vector<std::string>& out) {
  if (d == info.dim_sizes.size()) {
    out.push_back(prefix);
    return;
  }
  for (uint32_t i = 0; i < info.dim_sizes[d]; ++i) {
    AppendLeafSuffixes(info, d + 1,
                       prefix + "[" + std::to_string(info.dim_los[d] + i) + "]",
                       out);
  }
}

std::vector<std::string> MultiDimLeafSuffixes(const ArrayInfo& info) {
  std::vector<std::string> out;
  if (info.dim_sizes.size() < 2 ||
      info.dim_los.size() != info.dim_sizes.size()) {
    return out;
  }
  AppendLeafSuffixes(info, 0, "", out);
  return out;
}

static void CopyMultiDimLeaves(std::string_view dst_name, const ArrayInfo& dst,
                               std::string_view src_name, const ArrayInfo& src,
                               SimContext& ctx) {
  if (dst.dim_sizes != src.dim_sizes) return;
  std::vector<std::string> ds = MultiDimLeafSuffixes(dst);
  std::vector<std::string> ss = MultiDimLeafSuffixes(src);
  for (size_t i = 0; i < ds.size() && i < ss.size(); ++i) {
    auto* sv = ctx.FindVariable(std::string(src_name) + ss[i]);
    auto* dv = ctx.FindVariable(std::string(dst_name) + ds[i]);
    if (sv == nullptr || dv == nullptr) continue;
    dv->value = OwnRhsWords(sv->value, ctx.GetArena());
    dv->NotifyWatchers();
  }
}

void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                       std::string_view src_name, const ArrayInfo& src,
                       SimContext& ctx) {
  if (dst.dim_sizes.size() >= 2 || src.dim_sizes.size() >= 2) {
    CopyMultiDimLeaves(dst_name, dst, src_name, src, ctx);
    return;
  }
  uint32_t n = std::min(dst.size, src.size);
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t si =
        src.is_descending ? (src.lo + src.size - 1 - i) : (src.lo + i);
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto sn = std::string(src_name) + "[" + std::to_string(si) + "]";
    auto dn = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* sv = ctx.FindVariable(sn);
    auto* dv = ctx.FindVariable(dn);
    if (sv && dv) {
      dv->value = OwnRhsWords(sv->value, ctx.GetArena());
      dv->NotifyWatchers();
    }
  }
}

}  // namespace delta
