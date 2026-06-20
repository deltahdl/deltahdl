#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static uint64_t ResolveQueueIdx(const Expr* idx_expr, QueueObject* q,
                                SimContext& ctx, Arena& arena,
                                bool* has_xz = nullptr) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  uint64_t last = q->elements.empty() ? 0 : q->elements.size() - 1;
  dv->value = MakeLogic4VecVal(arena, 32, last);
  auto val = EvalExpr(idx_expr, ctx, arena);
  ctx.PopScope();
  if (has_xz) *has_xz = HasUnknownBits(val);
  return val.ToUint64();
}

static bool TryQueueSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;

  bool idx_xz = false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz) {
    out = MakeAllX(arena, q->elem_width);
    return true;
  }
  out = (idx < q->elements.size()) ? q->elements[idx]
                                   : MakeAllX(arena, q->elem_width);
  return true;
}

static const ArrayInfo* FindRootArrayInfo(const Expr* expr, SimContext& ctx) {
  const Expr* root = expr->base;
  while (root && root->kind == ExprKind::kSelect) root = root->base;
  return (root && root->kind == ExprKind::kIdentifier)
             ? ctx.FindArrayInfo(root->text)
             : nullptr;
}

// Reports whether the object a select reads from is four-state. An invalid
// bit-select address yields x on a four-state object but 0 on a two-state one,
// so the read result for an out-of-bounds or unknown index depends on this.
static bool SelectBaseIs4State(const Expr* expr, SimContext& ctx) {
  const Expr* root = expr->base;
  while (root && root->kind == ExprKind::kSelect) root = root->base;
  if (!root || root->kind != ExprKind::kIdentifier) return true;
  if (auto* info = ctx.FindArrayInfo(root->text)) return info->is_4state;
  if (auto* var = ctx.FindVariable(root->text)) return var->is_4state;
  return true;
}

static bool TryArrayElementSelect(const Expr* expr, uint64_t idx,
                                  SimContext& ctx, Arena& arena,
                                  Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* info = ctx.FindArrayInfo(expr->base->text);
  if (!info) return false;
  auto elem_name =
      std::string(expr->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(elem_name);
  if (!elem) {
    out = info->is_4state ? MakeAllX(arena, info->elem_width)
                          : MakeLogic4VecVal(arena, info->elem_width, 0);
    return true;
  }
  out = elem->value;
  return true;
}

static bool BuildCompoundName(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& name, bool* has_xz = nullptr) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundName(expr->base, ctx, arena, name, has_xz)) return false;
  auto idx_val = EvalExpr(expr->index, ctx, arena);

  if (HasUnknownBits(idx_val)) {
    if (has_xz) *has_xz = true;
    return false;
  }
  name += "[" + std::to_string(idx_val.ToUint64()) + "]";
  return true;
}

// Fills `out` with the default element value (x for four-state, 0 otherwise)
// for the array a compound select reads from, when the addressed element does
// not exist. Returns false when the root is not a recognized array.
static bool TryCompoundDefaultElem(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (auto* info = FindRootArrayInfo(expr, ctx)) {
    out = info->is_4state ? MakeAllX(arena, info->elem_width)
                          : MakeLogic4VecVal(arena, info->elem_width, 0);
    return true;
  }
  return false;
}

static bool TryCompoundArraySelect(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kSelect) return false;
  if (expr->index_end) return false;
  std::string compound;
  bool xz = false;
  if (!BuildCompoundName(expr, ctx, arena, compound, &xz)) {
    if (!xz) return false;
    return TryCompoundDefaultElem(expr, ctx, arena, out);
  }
  auto* elem = ctx.FindVariable(compound);
  if (!elem) return TryCompoundDefaultElem(expr, ctx, arena, out);
  out = elem->value;
  return true;
}

static bool TryArraySliceSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (!expr->index_end || !expr->base) return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* info = ctx.FindArrayInfo(expr->base->text);
  if (!info) return false;
  auto hi_val = EvalExpr(expr->index, ctx, arena).ToUint64();
  auto lo_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
  auto lo = std::min(hi_val, lo_val);
  auto hi = std::max(hi_val, lo_val);
  auto count = static_cast<uint32_t>(hi - lo + 1);
  uint32_t ew = info->elem_width;
  out = MakeLogic4Vec(arena, count * ew);
  for (uint32_t i = 0; i < count; ++i) {
    auto n = std::string(expr->base->text) + "[" + std::to_string(lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    auto val = v ? v->value.ToUint64() : 0;
    uint32_t bit_off = i * ew;
    out.words[bit_off / 64].aval |= (val & ((1ULL << ew) - 1))
                                    << (bit_off % 64);
  }
  return true;
}

static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, uint64_t idx,
                                uint64_t end_idx, Arena& arena) {
  auto lo = static_cast<uint32_t>(std::min(idx, end_idx));
  auto hi = static_cast<uint32_t>(std::max(idx, end_idx));
  uint32_t width = hi - lo + 1;
  uint64_t val = base_val.ToUint64() >> lo;
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  auto result = MakeLogic4VecVal(arena, width, val & mask);

  if (hi >= base_val.width && result.nwords > 0) {
    uint32_t first_oob = (base_val.width > lo) ? base_val.width - lo : 0;
    for (uint32_t b = first_oob; b < width && b < 64; ++b) {
      result.words[0].aval |= uint64_t{1} << b;
      result.words[0].bval |= uint64_t{1} << b;
    }
  }
  return result;
}

static Logic4Vec AssocDefault(const AssocArrayObject* aa, Arena& arena) {
  if (aa->has_default) return aa->default_value;
  return aa->is_4state ? MakeAllX(arena, aa->elem_width)
                       : MakeLogic4VecVal(arena, aa->elem_width, 0);
}

static std::string ExtractStringKey(const Logic4Vec& key) {
  uint32_t nb = key.width / 8;
  std::string s;
  s.reserve(nb);
  for (uint32_t i = nb; i > 0; --i) {
    uint32_t bi = i - 1;
    auto ch = static_cast<char>(
        (key.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
    if (ch != 0) s.push_back(ch);
  }
  return s;
}

static void WarnAssocMiss(const AssocArrayObject* aa, std::string_view name,
                          SimContext& ctx) {
  if (!aa->has_default)
    ctx.GetDiag().Warning({}, "associative array '" + std::string(name) +
                                  "': read of non-existent index");
}

static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto s = ExtractStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  if (it != aa->str_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx);
  return AssocDefault(aa, arena);
}

static Logic4Vec AssocReadInt(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto val = EvalExpr(idx_expr, ctx, arena);
  if (HasUnknownBits(val)) {
    // §7.8.6: an x/z index is an invalid read. A configured user default
    // suppresses the diagnostic and supplies the returned value (see §7.9.11),
    // matching the nonexistent-entry path in WarnAssocMiss.
    if (!aa->has_default)
      ctx.GetDiag().Warning({}, "associative array '" + std::string(name) +
                                    "': index contains x/z");
    return AssocDefault(aa, arena);
  }
  auto key =
      AssocIntKey(val, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  auto it = aa->int_data.find(key);
  if (it != aa->int_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx);
  return AssocDefault(aa, arena);
}

static bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* aa = ctx.FindAssocArray(expr->base->text);
  if (!aa) return false;
  out = aa->is_string_key
            ? AssocReadStr(aa, expr->index, expr->base->text, ctx, arena)
            : AssocReadInt(aa, expr->index, expr->base->text, ctx, arena);
  return true;
}

static Logic4Vec EvalPackedPartSelect(const Expr* expr, const Logic4Vec& base,
                                      uint64_t idx, SimContext& ctx,
                                      Arena& arena) {
  auto end_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
  if (expr->is_part_select_plus) {
    auto w = static_cast<uint32_t>(end_val);
    return EvalPartSelect(base, idx, idx + w - 1, arena);
  }
  if (expr->is_part_select_minus) {
    auto w = static_cast<uint32_t>(end_val);
    uint64_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
    return EvalPartSelect(base, lo, idx, arena);
  }
  return EvalPartSelect(base, idx, end_val, arena);
}

// Computes the result of a select whose index evaluates to x/z. A single-bit
// select over a known array yields that array's default element; a part-select
// yields all-x of the part width; a bit-select otherwise yields x or 0
// depending on whether the selected object is four-state.
static Logic4Vec EvalUnknownIndexSelect(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  if (!expr->index_end) {
    if (auto* info = FindRootArrayInfo(expr, ctx)) {
      return info->is_4state ? MakeAllX(arena, info->elem_width)
                             : MakeLogic4VecVal(arena, info->elem_width, 0);
    }
  }

  if (expr->index_end) {
    auto w =
        static_cast<uint32_t>(EvalExpr(expr->index_end, ctx, arena).ToUint64());
    return MakeAllX(arena, w > 0 ? w : 1);
  }
  return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                       : MakeLogic4VecVal(arena, 1, 0);
}

// Reads byte `idx` from a string value (indexed from the low end), returning an
// 8-bit result; out-of-range indices read as 0.
static Logic4Vec EvalStringByteSelect(const Logic4Vec& base_val, uint64_t idx,
                                      Arena& arena) {
  uint32_t nbytes = base_val.width / 8;
  if (idx >= nbytes) return MakeLogic4VecVal(arena, 8, 0);
  uint32_t byte_idx = nbytes - 1 - static_cast<uint32_t>(idx);
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  uint64_t ch =
      (word < base_val.nwords) ? (base_val.words[word].aval >> bit) & 0xFF : 0;
  return MakeLogic4VecVal(arena, 8, ch);
}

Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryQueueSelect(expr, ctx, arena, result)) return result;
  if (TryAssocSelect(expr, ctx, arena, result)) return result;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return EvalUnknownIndexSelect(expr, ctx, arena);
  uint64_t idx = idx_val.ToUint64();
  if (TryArrayElementSelect(expr, idx, ctx, arena, result)) return result;
  if (TryCompoundArraySelect(expr, ctx, arena, result)) return result;
  if (TryArraySliceSelect(expr, ctx, arena, result)) return result;
  auto base_val = EvalExpr(expr->base, ctx, arena);

  if (base_val.is_string && !expr->index_end)
    return EvalStringByteSelect(base_val, idx, arena);
  if (expr->index_end)
    return EvalPackedPartSelect(expr, base_val, idx, ctx, arena);
  if (idx >= base_val.width)
    return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                         : MakeLogic4VecVal(arena, 1, 0);
  return MakeLogic4VecVal(arena, 1, (base_val.ToUint64() >> idx) & 1);
}

}  // namespace delta
