#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

Logic4Vec NonexistentQueueElement(const QueueObject* q, Arena& arena) {
  return q->is_4state ? MakeAllX(arena, q->elem_width)
                      : MakeLogic4VecVal(arena, q->elem_width, 0);
}

int64_t SelectBoundValue(const Logic4Vec& val) {
  return val.is_signed ? SignExtend(val.ToUint64(), val.width)
                       : static_cast<int64_t>(val.ToUint64());
}

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

  // §7.10.1 makes two things an invalid index, and each needs a test of its
  // own. An index expression holding an x or z bit still converts to some
  // position, so a bounds test alone would let it read an element; it is
  // checked first, and the bounds decide the rest.
  bool idx_xz = false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz) {
    out = NonexistentQueueElement(q, arena);
    return true;
  }
  out = (idx < q->elements.size()) ? q->elements[idx]
                                   : NonexistentQueueElement(q, arena);
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
  // §6.16: an element of an array of strings is a string, and a string has no
  // declared width to fill with x or zero; one that was never written is "",
  // the empty string, of zero length. Both branches mark the value a string so
  // it reads back as one, since what reads a string reads that mark rather
  // than the width.
  bool elem_is_string = info->elem_type_kind == DataTypeKind::kString;
  if (!elem) {
    if (elem_is_string) {
      out = MakeLogic4VecVal(arena, 8, 0);
      out.is_string = true;
      return true;
    }
    out = info->is_4state ? MakeAllX(arena, info->elem_width)
                          : MakeLogic4VecVal(arena, info->elem_width, 0);
    return true;
  }
  out = elem->value;
  if (elem_is_string) out.is_string = true;
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
  // §7.4.5's Table 7-1 answers a read of a nonexistent entry by the element
  // type: 'x for a 4-state one and '0 for a 2-state one. The two readers below
  // reach that table for an element the slice names and the array does not
  // hold, and this is what tells them which row -- ArrayInfo carries it and
  // neither could ask, so both answered the 2-state row for every array.
  bool is_4state;
};

// §7.4.5's Table 7-1, "Value read from a nonexistent array entry": 'x for a
// 4-state integral element type and '0 for a 2-state one. Said once here for
// the two slice readers below, which answer the same table
// TryArrayElementSelect and TryCompoundDefaultElem above answer for a single
// element of the same array.
static Logic4Vec ElementDefault(bool is_4state, uint32_t elem_width,
                                Arena& arena) {
  return is_4state ? MakeAllX(arena, elem_width)
                   : MakeLogic4VecVal(arena, elem_width, 0);
}

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
  out.is_4state = info->is_4state;
  // A compound name only reaches an array through the leaves it was built to
  // reach, so an absent leaf means this is not that array; a direct name has
  // already been matched against the array itself, and an absent element there
  // is an out-of-range read the loops below answer from Table 7-1.
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
//
// Each element is answered as a value, not as a handle on the element it was
// read from. §6.8 makes that element its own storage -- "A variable is an
// abstraction of a data storage element. A variable shall store a value from
// one assignment to the next" -- and an array element is such an element, so a
// run pushed as `v->value` handed a whole row of them out by pointer. Every
// caller stores what it collects, into a destination slice's elements, a
// destination array's, or a queue's, and none reads back through the entries,
// so the copy is taken once here where the run is produced rather than at each
// of those stores. The fallback element is built fresh and needs none.
//
// This pair is quiet where it is made: no store on these paths coerces, so
// nothing happens inside the statement that read the source, and the shared
// buffer only shows on the next write to either side -- a resize that keeps
// the words at equal widths and coerces through them, or a deposit into a
// packed member that lands in both.
bool CollectUnpackedSliceElements(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  UnpackedSliceRun run;
  if (!ResolveUnpackedSliceRun(expr, ctx, arena, run)) return false;
  for (uint32_t i = 0; i < run.count; ++i) {
    uint32_t idx =
        run.is_descending ? (run.lo + run.count - 1 - i) : (run.lo + i);
    auto n = run.base + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(n);
    // §7.4.5: "Reading from an unpacked array of any kind with an invalid index
    // shall return the value specified in Table 7-1", which gives a 4-state
    // element 'x and only a 2-state one '0. This is the same answer
    // TryArrayElementSelect and TryCompoundDefaultElem give for the element
    // spelling of the same read.
    out.push_back(v ? OwnRhsWords(v->value, arena)
                    : ElementDefault(run.is_4state, run.elem_width, arena));
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
    // The bit-field primitives rather than 64-bit integer arithmetic, which is
    // four answers at once. ExtractBitField carries the bval plane, so §6.3.1's
    // "All bits of 4-state vectors can be independently set to one of the four
    // basic values" survives the read where ToUint64 projected `aval & ~bval`
    // and every x and z arrived as 0; it reads every word, where ToUint64
    // returns words[0] alone. DepositBitField resolves the word each bit
    // belongs in, where `|=` into `out.words[bit_off / 64]` wrote one word per
    // element and dropped the part of an element that straddled the boundary.
    // And no mask is left to shift: `(1ULL << ew) - 1` on a 64-bit element
    // shifted a uint64_t by 64, which is undefined behaviour rather than a wide
    // zero -- on x86-64 the count is taken modulo 64, so the mask came out 0
    // and the whole slice read as zero. This is the instrument 7e036a31f moved
    // the other two select read paths in this file onto, and it takes §7.4.5's
    // Table 7-1 default in the same deposit.
    Logic4Vec elem = v != nullptr ? ExtractBitField(arena, v->value, 0, ew)
                                  : ElementDefault(run.is_4state, ew, arena);
    DepositBitField(out, i * ew, elem, ew);
  }
  return true;
}

// §11.5.1: "Part-selects that are partially out of range shall, when read,
// return x for the bits that are out of range." `lo_off` is the storage offset
// the result's least significant bit was read from; it is negative when the
// select runs off the low end of the value, and `lo_off + width` exceeds the
// value's width when it runs off the high end.
//
// This marking and the copy in EvalPartSelect below divide the result between
// them: the copy owns the positions the value holds, this owns every other
// one, which is why the `continue` is here and why neither writes where the
// other does. See that function's comment for the copy's half of the bargain.
// Both now resolve the word a result position lives in, so a select wider than
// one word is marked above position 63 as well; the loop used to stop at 64
// and leave the overhang of a partially out of range select at a known 0
// there. An out-of-range bit reads x, not z, and Logic4Word spells x with aval
// and bval both set, so the bit goes into both planes.
static void MarkOutOfRangeBitsX(Logic4Vec* result, uint32_t base_width,
                                int64_t lo_off, uint32_t width) {
  if (result->nwords == 0) return;
  for (uint32_t b = 0; b < width; ++b) {
    int64_t off = lo_off + b;
    if (off >= 0 && off < static_cast<int64_t>(base_width)) continue;
    result->words[b / 64].aval |= uint64_t{1} << (b % 64);
    result->words[b / 64].bval |= uint64_t{1} << (b % 64);
  }
}

// Reads the bits between two storage offsets of `base_val`, either of which may
// lie outside it.
//
// §11.5.1 gives a select the value the bits it addresses hold, and §6.3.1 sets
// every bit of a 4-state vector independently to one of the four basic values,
// so a bit holding x reads x and one holding z reads z. This function and the
// bit-select ending EvalSelect both used to read through Logic4Vec::ToUint64,
// the 2-state projection: it masks by ~bval, so an x and a z alike arrived as
// 0, and MakeLogic4VecVal sets no bval, so neither could leave. `a[0:0]` and
// `a[0]` name one window of one variable and have to answer alike; both
// answered a known 0. ToUint64 returns words[0] alone besides, so neither
// reached a bit at offset 64 or above -- this one clamped its shift to 63 and
// read the top of the first word, the bit-select shifted a single word by its
// own width, which C++ leaves undefined. ExtractBitField copies a window bit
// by bit, carrying the bval plane and indexing the word each bit lives in, and
// it is what TryPackedElementSelect below already read its own one-element
// window with. It fills positions at or beyond `base_val.width` with 0 rather
// than x, so the marking still runs after it; the marking writes only
// positions outside the value, which the copy leaves clear, so the two agree
// on every bit rather than contending for any.
static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, int64_t idx,
                                int64_t end_idx, Arena& arena) {
  int64_t lo = std::min(idx, end_idx);
  int64_t hi = std::max(idx, end_idx);
  auto width = static_cast<uint32_t>(hi - lo + 1);
  auto result = MakeLogic4Vec(arena, width);
  // The window's own bits start at the first of them the value holds, and land
  // that far up in the result when the select runs off the value's low end. A
  // window lying wholly below the value reads none of it at all.
  int64_t start = std::max<int64_t>(lo, 0);
  if (start <= hi) {
    auto n = static_cast<uint32_t>(hi - start + 1);
    DepositBitField(
        result, static_cast<uint32_t>(start - lo),
        ExtractBitField(arena, base_val, static_cast<uint32_t>(start), n), n);
  }
  MarkOutOfRangeBitsX(&result, base_val.width, lo, width);
  return result;
}

static Logic4Vec AssocDefault(const AssocArrayObject* aa, Arena& arena) {
  if (aa->has_default) return aa->default_value;
  return aa->is_4state ? MakeAllX(arena, aa->elem_width)
                       : MakeLogic4VecVal(arena, aa->elem_width, 0);
}

// `loc` is where the index was written, which the report names: the array
// object carries no position and the name is a string.
static void WarnAssocMiss(const AssocArrayObject* aa, std::string_view name,
                          SimContext& ctx, SourceLoc loc) {
  if (!aa->has_default)
    ctx.GetDiag().Warning(loc,
                          "associative array '" + std::string(name) +
                              "': read of non-existent index",
                          Subclause("7.8.6"));
}

static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto s = AssocStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  if (it != aa->str_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx, idx_expr->range.start);
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
          idx_expr->range.start,
          "associative array '" + std::string(name) + "': index contains x/z",
          Subclause("7.8.6"));
    return AssocDefault(aa, arena);
  }
  auto key =
      AssocIntKey(val, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  auto it = aa->int_data.find(key);
  if (it != aa->int_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx, idx_expr->range.start);
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

// §11.5.1: how wide a non-indexed part-select is when one of its two bounds is
// x or z. "The width of a part-select is always constant", and with one bound
// unknown the span is not a number the expression states, so what bounds it is
// the declaration: the pair runs from the more significant index to the less
// significant one, and the widest such select the object admits runs from the
// known bound -- brought inside the range, since a bound outside it addresses
// no bit -- to the end the unknown one lies toward. An unknown first bound
// therefore spans up to the most significant index and an unknown second bound
// down to the least significant one, and a known bound sitting at that end
// leaves the single bit the two offsets then name.
static uint32_t UnknownBoundPartSelectWidth(const PackedRange& range,
                                            int64_t known_bound,
                                            bool unknown_is_more_significant) {
  int64_t known_off = range.OffsetOf(range.Clamp(known_bound));
  int64_t far_off =
      unknown_is_more_significant ? range.OffsetOf(range.left) : 0;
  return static_cast<uint32_t>(std::max(known_off, far_off) -
                               std::min(known_off, far_off) + 1);
}

static Logic4Vec EvalPackedPartSelect(const Expr* expr, const Logic4Vec& base,
                                      int64_t idx, SimContext& ctx,
                                      Arena& arena) {
  auto end = EvalExpr(expr->index_end, ctx, arena);
  auto range = SelectBaseRange(expr->base, base.width, ctx, arena);
  // §11.5.1: "a part-select that is x or z shall yield the value x when read",
  // and the clause makes both bounds of `vect[msb_expr:lsb_expr]` addresses --
  // "Both msb_expr and lsb_expr shall be constant integer expressions" -- so an
  // unknown second bound is as much an unknown address as an unknown first one.
  // Only the first was asked about, on the way in to this function, and the
  // second reached SelectBoundValue, whose Logic4Vec::ToUint64 is the
  // "4-state -> integer projection" its own comment in src/common/types.cpp
  // calls it: x and z both arrived as the index 0, and the select silently
  // became a different, well-formed one. On a `logic [7:0] a = 8'hA5`,
  // `a[3 : 1'bx]` was read as `a[3:0]` and answered 4'b0101. SelectStorageBits
  // (statement_assign.cpp), which every writer of a select now goes through,
  // has asked this of both bounds all along, so the read was the one direction
  // where the two bounds were not alike. The second expression of an indexed
  // part-select is its width rather than an address, and an unknown one is no
  // more a width than an unknown bound is an address -- §11.5.1 has it "shall
  // be a positive constant integer expression" -- so it takes the same route,
  // as it does at the writers.
  if (HasUnknownBits(end)) {
    return MakeAllX(arena, UnknownBoundPartSelectWidth(
                               range, idx,
                               /*unknown_is_more_significant=*/false));
  }
  auto target = PartSelectTargetIndices(idx, SelectBoundValue(end),
                                        expr->is_part_select_plus,
                                        expr->is_part_select_minus);
  return EvalPartSelect(base, range.OffsetOf(target.first),
                        range.OffsetOf(target.second), arena);
}

// §11.5.1: how wide a part-select is whose first index is x or z. The clause
// gives the second expression two meanings and the part-select flags are the
// whole of what says which one this select carries: for `[base +: width]` and
// `[base -: width]` it is the width, which "shall be a positive constant
// integer expression", and for `[msb_expr:lsb_expr]` it is the second index,
// with the width being the span the two indices name. Reading it as a width for
// both is what let `a[1'bx : -2]` ask for a vector of 4294967294 bits, since
// SelectBoundValue's -2 was a width of 4294967294 to a uint32_t cast.
//
// The first index is x, so the span is not a number the expression states, and
// §11.5.1 nonetheless makes it constant: "The width of a part-select is always
// constant." What bounds it is the declaration. The clause's first index is the
// more significant end of the pair, so the widest such select the object admits
// runs from the known second index -- brought inside the range, since a bound
// outside it addresses no bit of the object -- up to the most significant index
// there is. A second index at or past that end leaves the one bit the minimum
// below keeps, which is the same answer §11.5.1 gives a select "completely out
// of the address bounds": the value x.
//
// A base with no declaration of its own is left at the implicit empty range
// rather than evaluated for its width, since this arm runs before the base is
// read and evaluating it here would run its side effects a second time.
static uint32_t UnknownIndexPartSelectWidth(const Expr* expr, SimContext& ctx,
                                            Arena& arena) {
  int64_t end_val = SelectBoundValue(EvalExpr(expr->index_end, ctx, arena));
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    return end_val > 0 ? static_cast<uint32_t>(end_val) : 1;
  }
  auto range = SelectBaseRange(expr->base, /*width=*/0, ctx, arena);
  return UnknownBoundPartSelectWidth(range, end_val,
                                     /*unknown_is_more_significant=*/true);
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
    return MakeAllX(arena, UnknownIndexPartSelectWidth(expr, ctx, arena));
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
  auto declared_idx = SelectBoundValue(idx_val);
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
  // One bit is a window of one, read the way EvalPartSelect above reads the
  // other spelling of it and for the reasons set out there.
  auto off = static_cast<uint32_t>(range.OffsetOf(declared_idx));
  return ExtractBitField(arena, base_val, off, 1);
}

}  // namespace delta
