#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/packed_select.h"
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

  // §7.10.1: an invalid queue index (an x/z 4-state expression, or a position
  // outside 0..$) makes the read return the value appropriate for a nonexistent
  // element of the queue's element type, per Table 7-1 in §7.4.5. That value is
  // x for a 4-state element type but '0 for a 2-state one, so it must respect
  // the queue's own state-ness rather than always yielding x.
  auto nonexistent = [&] {
    return q->is_4state ? MakeAllX(arena, q->elem_width)
                        : MakeLogic4VecVal(arena, q->elem_width, 0);
  };
  bool idx_xz = false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz) {
    out = nonexistent();
    return true;
  }
  out = (idx < q->elements.size()) ? q->elements[idx] : nonexistent();
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
  if (elem) {
    out = elem->value;
    return true;
  }
  // The full compound name is not a variable. If the base (all indices but the
  // last) names a real packed element, the trailing index is a bit-select of
  // that element per §11.5.2, not a further array dimension: return false so
  // EvalSelect falls through to the bit-select path. Only when the addressed
  // array element itself is absent is this a genuine out-of-bounds read that
  // defaults to x/0.
  std::string parent;
  if (BuildCompoundName(expr->base, ctx, arena, parent) &&
      ctx.FindVariable(parent)) {
    return false;
  }
  return TryCompoundDefaultElem(expr, ctx, arena, out);
}

std::pair<uint32_t, uint32_t> SelectRange(const Expr* expr, SimContext& ctx,
                                          Arena& arena) {
  auto start =
      static_cast<uint32_t>(EvalExpr(expr->index, ctx, arena).ToUint64());
  auto end_val =
      static_cast<uint32_t>(EvalExpr(expr->index_end, ctx, arena).ToUint64());
  if (expr->is_part_select_plus) return {start, end_val};
  if (expr->is_part_select_minus) return {start - end_val + 1, end_val};
  auto lo = std::min(start, end_val);
  return {lo, std::max(start, end_val) - lo + 1};
}

// §7.4.5: the run of elements an unpacked-array slice addresses. The slice may
// be written on the array itself (`arr[lo:hi]`) or on one dimension of a
// multidimensional array whose other dimensions carry single index values
// (`A[i][lo:hi]`) -- "Slices of an array can only apply to one dimension, but
// other dimensions can have single index values in an expression". Either way
// the addressed elements are stored as leaf variables under `base`, so the two
// forms differ only in how that name is spelled.
struct UnpackedSliceRun {
  std::string base;
  uint32_t lo;
  uint32_t count;
  uint32_t elem_width;
  // The declared direction of the array the run is taken from. `lo` is the
  // numerically lowest index either way, so this is what says which end of the
  // run the slice's first element sits at.
  bool is_descending;
};

// Names the run `expr` addresses, or declines when `expr` is not a slice of an
// unpacked array. A compound base that is itself a stored packed element is not
// an array: there the index pair is a bit part-select of that element per
// §11.5.2, so it is declined and left to the packed part-select path.
static bool ResolveUnpackedSliceRun(const Expr* expr, SimContext& ctx,
                                    Arena& arena, UnpackedSliceRun& out) {
  if (!expr || expr->kind != ExprKind::kSelect) return false;
  if (!expr->index_end || !expr->base) return false;
  const ArrayInfo* info = nullptr;
  bool compound = expr->base->kind == ExprKind::kSelect;
  if (expr->base->kind == ExprKind::kIdentifier) {
    out.base = std::string(expr->base->text);
    info = ctx.FindArrayInfo(out.base);
  } else if (compound) {
    if (!BuildCompoundName(expr->base, ctx, arena, out.base)) return false;
    if (ctx.FindVariable(out.base)) return false;
    info = FindRootArrayInfo(expr, ctx);
  }
  if (!info) return false;
  // §7.4.5: the second operand of an indexed part-select is a width, not an
  // end point, so the addressed run is taken from the form the expression was
  // written in rather than from the two operands alone.
  auto [lo, count] = SelectRange(expr, ctx, arena);
  out.lo = lo;
  out.count = count;
  out.elem_width = info->elem_width;
  out.is_descending = info->is_descending;
  // A compound name only reaches an array through the leaves it was built to
  // reach, so an absent leaf means this is not that array; a direct name has
  // already been matched against the array itself, and an absent element there
  // is an out-of-range read that the loop below reports as zero.
  return !compound ||
         ctx.FindVariable(out.base + "[" + std::to_string(lo) + "]") != nullptr;
}

// §7.4.5: "A slice name of an unpacked array is an unpacked array", and §7.6
// pairs one unpacked array with another by position: "Correspondence between
// elements is determined by the left-to-right order of elements in each array",
// so `int A[7:0]` and `int B[1:8]` assign `B[1]` to `A[7]`. The run is
// therefore appended in the declared order of the array it comes from rather
// than by ascending index. §7.4.5's own `busA[7:6]` is written on a `busA
// [7:0]`, whose first element is `busA[7]`; that slice contributes `busA[7]`
// first. Reversing both ends of a copy changes nothing, so this only becomes
// visible against a destination that runs the other way.
bool CollectUnpackedSliceElements(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  UnpackedSliceRun run;
  if (!ResolveUnpackedSliceRun(expr, ctx, arena, run)) return false;
  for (uint32_t i = 0; i < run.count; ++i) {
    uint32_t idx =
        run.is_descending ? (run.lo + run.count - 1 - i) : (run.lo + i);
    auto n = run.base + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(n);
    out.push_back(v ? v->value : MakeLogic4VecVal(arena, run.elem_width, 0));
  }
  return true;
}

// Reads an unpacked-array slice as one packed value, the concatenation of its
// elements. This is what a context expecting a single value gets; a context
// that can hold the unpacked array the clause calls for reads the same run
// through CollectUnpackedSliceElements instead.
static bool TryArraySliceSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  UnpackedSliceRun run;
  if (!ResolveUnpackedSliceRun(expr, ctx, arena, run)) return false;
  uint32_t ew = run.elem_width;
  out = MakeLogic4Vec(arena, run.count * ew);
  for (uint32_t i = 0; i < run.count; ++i) {
    auto n = run.base + "[" + std::to_string(run.lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    auto val = v ? v->value.ToUint64() : 0;
    uint32_t bit_off = i * ew;
    out.words[bit_off / 64].aval |= (val & ((1ULL << ew) - 1))
                                    << (bit_off % 64);
  }
  return true;
}

// §11.5.1: "Part-selects that are partially out of range shall, when read,
// return x for the bits that are out of range." `lo_off` is the storage offset
// the result's least significant bit was read from; it is negative when the
// select runs off the low end of the value, and `lo_off + width` exceeds the
// value's width when it runs off the high end.
static void MarkOutOfRangeBitsX(Logic4Vec* result, uint32_t base_width,
                                int64_t lo_off, uint32_t width) {
  if (result->nwords == 0) return;
  for (uint32_t b = 0; b < width && b < 64; ++b) {
    int64_t off = lo_off + b;
    if (off >= 0 && off < static_cast<int64_t>(base_width)) continue;
    result->words[0].aval |= uint64_t{1} << b;
    result->words[0].bval |= uint64_t{1} << b;
  }
}

// Reads the bits between two storage offsets of `base_val`, either of which may
// lie outside it.
static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, int64_t idx,
                                int64_t end_idx, Arena& arena) {
  int64_t lo = std::min(idx, end_idx);
  int64_t hi = std::max(idx, end_idx);
  auto width = static_cast<uint32_t>(hi - lo + 1);
  // Both shifts are held inside a word: a select far enough outside the value
  // to need more than that reads no bits of it at all, and the out-of-range
  // marking below covers the whole result.
  uint64_t val = base_val.ToUint64() >> std::clamp<int64_t>(lo, 0, 63);
  // Bits read from the value sit that far up in the result when the select
  // starts below the value's least significant bit.
  if (lo < 0) val <<= std::clamp<int64_t>(-lo, 0, 63);
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  auto result = MakeLogic4VecVal(arena, width, val & mask);
  MarkOutOfRangeBitsX(&result, base_val.width, lo, width);
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
    ctx.GetDiag().Warning({},
                          "associative array '" + std::string(name) +
                              "': read of non-existent index",
                          Clause::Unread());
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
      ctx.GetDiag().Warning(
          {},
          "associative array '" + std::string(name) + "': index contains x/z",
          Clause::Unread());
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

// §11.5.1: the range a select's indices are resolved against. When the select
// names a vector it is that vector's declared range, since "the actual bit that
// is accessed by an address is, in part, determined by the declaration"; for
// anything else -- a concatenation, a function result, a struct member -- the
// value carries no declaration of its own and is addressed as [width-1:0].
static PackedRange SelectBaseRange(const Expr* base, uint32_t width,
                                   SimContext& ctx, Arena& arena) {
  const Variable* var = nullptr;
  if (base && base->kind == ExprKind::kIdentifier) {
    var = ctx.FindVariable(base->text);
  } else if (base && base->kind == ExprKind::kSelect) {
    // An element of an unpacked array is a vector in its own right, declared
    // with the array's element type and so with that type's range.
    std::string name;
    if (BuildCompoundName(base, ctx, arena, name)) var = ctx.FindVariable(name);
  }
  return var ? var->BitSelectRange() : PackedRange::Implicit(width);
}

static Logic4Vec EvalPackedPartSelect(const Expr* expr, const Logic4Vec& base,
                                      int64_t idx, SimContext& ctx,
                                      Arena& arena) {
  auto end_val =
      static_cast<int64_t>(EvalExpr(expr->index_end, ctx, arena).ToUint64());
  auto target = PartSelectTargetIndices(expr, idx, end_val);
  auto range = SelectBaseRange(expr->base, base.width, ctx, arena);
  return EvalPartSelect(base, range.OffsetOf(target.first),
                        range.OffsetOf(target.second), arena);
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

// §7.4.1: a single-index select of a packed multidimensional array selects an
// outermost element (the inner-dimension width) as an unsigned vector, not a
// single bit. Returns the element value when `expr` names such an array.
static std::optional<Logic4Vec> TryPackedElementSelect(
    const Expr* expr, int64_t idx, const Logic4Vec& base_val, SimContext& ctx,
    Arena& arena) {
  if (expr->index_end || !expr->base ||
      expr->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  auto* var = ctx.FindVariable(expr->base->text);
  if (!var || var->packed_elem_width <= 1) return std::nullopt;
  uint32_t w = var->packed_elem_width;
  auto range = var->DeclaredRange();
  uint64_t off = range.Contains(idx)
                     ? static_cast<uint64_t>(range.OffsetOf(idx)) * w
                     : base_val.width;
  if (off >= base_val.width)
    return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, w)
                                         : MakeLogic4VecVal(arena, w, 0);
  return ExtractBitField(arena, base_val, static_cast<uint32_t>(off), w);
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
  auto declared_idx = static_cast<int64_t>(idx);
  if (expr->index_end)
    return EvalPackedPartSelect(expr, base_val, declared_idx, ctx, arena);
  if (auto elem =
          TryPackedElementSelect(expr, declared_idx, base_val, ctx, arena))
    return *elem;
  // §11.5.1: which bit a bit-select addresses follows from the declared range
  // of what is being selected from, so it is resolved against that range rather
  // than taken as a storage offset.
  auto range = SelectBaseRange(expr->base, base_val.width, ctx, arena);
  if (!range.Contains(declared_idx))
    return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                         : MakeLogic4VecVal(arena, 1, 0);
  auto off = static_cast<uint32_t>(range.OffsetOf(declared_idx));
  return MakeLogic4VecVal(arena, 1, (base_val.ToUint64() >> off) & 1);
}

}  // namespace delta
