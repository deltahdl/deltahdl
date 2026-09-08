#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

static std::string_view LhsIdentName(const Expr* lhs) {
  while (lhs) {
    if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
    if (lhs->kind == ExprKind::kSelect && lhs->base) {
      lhs = lhs->base;
      continue;
    }
    break;
  }
  return {};
}

void CoerceTo2State(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

// A right-hand value that owns its words, for a store to keep.
//
// §6.8: "A variable is an abstraction of a data storage element. A variable
// shall store a value from one assignment to the next." Two variables are two
// storage elements, and no clause has to forbid them sharing one buffer: the
// object model the clause describes already makes them separate. EvalExpr
// answers a bare identifier with the variable's own Logic4Vec (EvalIdentifier,
// evaluation.cpp), an element select with the element variable's own vec
// (eval_select.cpp), and a Logic4Vec copies its `words` pointer rather than the
// words it points at. ResizeToWidth returns its argument untouched when the
// widths already match, so `y = x` at equal widths stored x's buffer in y.
//
// That is not a latent hazard waiting for a later write. The very next line of
// every one of these stores is `if (!var->is_4state) CoerceTo2State(...)`,
// which writes in place: on `logic [7:0] x; bit [7:0] y; y = x;` the coercion
// reached back through the alias and cleared x's own x and z bits, inside the
// statement that only read x.
//
// The copy is taken where the value is produced rather than at each store, so
// every store downstream of a production point is already safe and none of them
// has to know. A production point pays one copy for a statement; the stores are
// six, and several of them run per element.
//
// ExtractBitField copies the words -- multi-word safe, and it carries the bval
// plane, so an x or z survives the copy -- but it builds its result with
// MakeLogic4Vec, which leaves is_real, is_signed and is_string false. All three
// are read after this point and are restored beside the words:
// ConvertRealOnAssign branches on is_real to convert rather than reinterpret a
// real's bits, ResizeToWidth sign-extends on is_signed, and a value stored into
// a class property keeps its is_string for whatever later reads the property as
// text.
//
// This is the blocking mirror of SampleNbaRhs
// (statement_assign_nonblocking.cpp), which §10.4.2's sampling needed for the
// same reason.
Logic4Vec OwnRhsWords(const Logic4Vec& val, Arena& arena) {
  Logic4Vec copy = ExtractBitField(arena, val, 0, val.width);
  copy.is_real = val.is_real;
  copy.is_signed = val.is_signed;
  copy.is_string = val.is_string;
  return copy;
}

static void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena) {
  // §10.6.2: "A force statement to a variable shall override a procedural
  // assignment ... until a release procedural statement is executed on the
  // variable." Every other writer a blocking assignment reaches declines here;
  // this one is reached only by §11.4.1's compound operators, which no case
  // asked the rule of, so `force x = 8'd50; x += 8'd10;` read 60. A force
  // establishes its own value by writing the field directly rather than through
  // this, so nothing a force or a release needs is declined.
  if (var->is_forced) return;
  var->value = ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena) {
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) {
    WriteVar(elem, rhs_val, arena);
    return true;
  }
  if (TryQueueIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (TryAssocIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  // §7.8.7: `aa[3][7:0] = v` targets bits of an associative array element, so
  // the element is allocated and written. TryResolveCompoundElement below
  // would otherwise fabricate a plain variable named "aa[3]" and divert the
  // write into it, leaving the array untouched.
  if (TryWriteAssocElementBits(lhs, rhs_val, ctx, arena)) return true;
  // §11.5.1: `c.p[7:0] = v` targets bits of a class property, which lives in
  // the object's property map rather than in a variable, so no writer below
  // can reach it and ResolveLhsVariable answers null for the name it rebuilds.
  if (TryWriteClassPropertyBits(lhs, rhs_val, ctx, arena)) return true;
  bool absent_element = false;
  if (auto* compound =
          TryResolveCompoundElement(lhs, ctx, arena, &absent_element)) {
    WriteVar(compound, rhs_val, arena);
    return true;
  }
  // §7.4.5: a write to an array with an invalid index performs no operation.
  // Handled here rather than left to fall through, because ResolveLhsVariable
  // below walks `a[i][j]` down to the variable named `a` -- the element-width
  // carrier no element is stored in -- and WriteBitSelect would then read the
  // last index as a bit position of it.
  if (absent_element) return true;
  auto* var = ResolveLhsVariable(lhs, ctx);

  if (var && lhs->kind == ExprKind::kSelect && lhs->base && !lhs->index_end) {
    auto base_name = LhsIdentName(lhs->base);
    if (!base_name.empty() && ctx.IsStringVariable(base_name)) {
      auto idx_val = EvalExpr(lhs->index, ctx, arena);
      if (!HasUnknownBits(idx_val)) {
        StringWriteByte(var, static_cast<uint32_t>(idx_val.ToUint64()),
                        static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF), arena);
        var->NotifyWatchers();
      }
      return true;
    }
  }
  if (var) {
    WriteBitSelect(var, lhs, rhs_val, ctx, arena);
  }
  return true;
}

const Expr* UnwrapTypedPattern(const Expr* expr) {
  if (expr->kind == ExprKind::kCast && expr->lhs &&
      expr->lhs->kind == ExprKind::kAssignmentPattern)
    return expr->lhs;
  return expr;
}

bool IsConcatLhs(const Expr* lhs) {
  if (!lhs) return false;
  const Expr* pat = UnwrapTypedPattern(lhs);
  return pat->kind == ExprKind::kConcatenation ||
         pat->kind == ExprKind::kAssignmentPattern;
}

// §11.6.1 sizes an assignment's context from its left-hand side and §10.7 makes
// that size the right-hand expression's context, which is the rule
// ConcatLhsElemWidth states one element at a time. The element rule and the
// context rule are one rule, written twice: this copy lacked the select clause
// and answered the whole of `a` for `a[3:0]`, so `{a[3:0], b} = a*b/c` divided
// in a sixteen-bit context where §11.6.1 gives the concatenation twelve. Said
// once, the context width and the width UnpackConcatLhs cuts the value into
// cannot drift apart.
uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx, Arena& arena) {
  if (!lhs) return 0;
  return ConcatLhsElemWidth(lhs, ctx, arena);
}

// §11.9: the struct layout of the union member a tagged expression names, or
// null when the union declares no such member with a layout of its own.
static const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                                std::string_view member) {
  for (const auto& field : sinfo.fields) {
    if (field.name == member && field.nested) return field.nested;
  }
  return nullptr;
}

Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  uint32_t ctx_width = LhsContextWidth(stmt->lhs, ctx, arena);
  if (!stmt->rhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  }
  // §11.9: the member value of a tagged expression may be a §10.9.2 structure
  // assignment pattern (e.g. `i1 = tagged Add '{e1, 4, ed}`). Pack that pattern
  // against the union member's own struct layout, not the union as a whole, so
  // each field expression is coerced to its member's width instead of being
  // concatenated at its self-determined width.
  if (stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs &&
      stmt->rhs->lhs && stmt->rhs->lhs->kind == ExprKind::kAssignmentPattern) {
    const auto* sinfo = ctx.GetVariableStructType(stmt->lhs->text);
    if (const StructTypeInfo* member =
            sinfo ? TaggedMemberLayout(*sinfo, stmt->rhs->rhs->text) : nullptr)
      return EvalStructPatternValue(stmt->rhs->lhs, member, ctx, arena);
  }
  auto* inner = UnwrapTypedPattern(stmt->rhs);
  // §10.9.2: both keyed and positional structure patterns are evaluated against
  // the target's member layout so each member expression is coerced to its
  // member's type; only route when the target is actually a struct.
  if (inner->kind != ExprKind::kAssignmentPattern)
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  auto* sinfo = ctx.GetVariableStructType(stmt->lhs->text);
  if (!sinfo) return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  return EvalStructPatternValue(inner, sinfo, ctx, arena);
}

// §7.4.6: destination window of an unpacked-array slice assignment, i.e. the
// elements `base[dst_lo .. dst_lo+dst_count)` each `elem_width` bits wide.
struct UnpackedSliceTarget {
  std::string_view base;
  uint32_t dst_lo;
  uint32_t dst_count;
  uint32_t elem_width;
  // The declared direction of the array the window is cut from. `dst_lo` is the
  // numerically lowest index either way, so this is what says which end of the
  // window receives the first source element.
  bool is_descending;
};

// The index that position `i` of the destination window occupies, counting
// positions in the declared order of the array rather than by ascending index.
static uint32_t SliceTargetIndex(const UnpackedSliceTarget& dst, uint32_t i) {
  return dst.is_descending ? (dst.dst_lo + dst.dst_count - 1 - i)
                           : (dst.dst_lo + i);
}

// When no element-wise source was collected, evaluate the rhs as a single
// packed value and split it into `dst.dst_count` element-width slices.
//
// The concatenation a slice reads as puts the lowest-indexed element in the low
// bits, so the low field belongs to index `dst_lo` whichever way the array
// runs. The writer places source position i by declared order, so on a
// descending destination the low field is the last position rather than the
// first, and the fields are emitted from the top down to land where they came
// from.
static void FillSliceSourceFromPacked(const Stmt* stmt,
                                      const UnpackedSliceTarget& dst,
                                      SimContext& ctx, Arena& arena,
                                      std::vector<Logic4Vec>& src) {
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  uint32_t elem_width = dst.elem_width;
  uint64_t mask =
      (elem_width >= 64) ? ~uint64_t{0} : (uint64_t{1} << elem_width) - 1;
  for (uint32_t i = 0; i < dst.dst_count; ++i) {
    uint32_t field = dst.is_descending ? (dst.dst_count - 1 - i) : i;
    src.push_back(MakeLogic4VecVal(
        arena, elem_width, (val.ToUint64() >> (field * elem_width)) & mask));
  }
}

// Write the collected source elements into the destination slice elements
// `dst.base[dst.dst_lo .. dst.dst_lo+dst.dst_count)`, resizing/coercing as for
// a scalar write. Source position i fills the window's i'th element in the
// destination array's declared order: §7.4.5 makes both sides unpacked arrays,
// and §7.6 pairs one with another by position rather than by index --
// "Correspondence between elements is determined by the left-to-right order of
// elements in each array". §7.6 also settles the window itself, since "an
// assignment where the left-hand side contains a slice is treated as a single
// assignment to the entire slice".
static void WriteUnpackedSliceElements(const UnpackedSliceTarget& dst,
                                       const std::vector<Logic4Vec>& src,
                                       SimContext& ctx, Arena& arena) {
  for (uint32_t i = 0; i < dst.dst_count && i < src.size(); ++i) {
    auto n = std::string(dst.base) + "[" +
             std::to_string(SliceTargetIndex(dst, i)) + "]";
    auto* var = ctx.FindVariable(n);
    if (!var) continue;
    var->value = ResizeToWidth(src[i], var->value.width, arena);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  }
}

static bool TryUnpackedSliceAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* lhs = stmt->lhs;
  if (lhs->kind != ExprKind::kSelect || !lhs->index_end) return false;
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* dst_info = ctx.FindArrayInfo(lhs->base->text);
  if (!dst_info) return false;
  auto [dst_lo, dst_count] = SelectRange(lhs, ctx, arena);
  UnpackedSliceTarget dst{lhs->base->text, dst_lo, dst_count,
                          dst_info->elem_width, dst_info->is_descending};
  std::vector<Logic4Vec> src;
  // The collector answers each element with a copy of its own, so its entries
  // are the destination's to keep; the packed fallback builds its fields fresh
  // and owns them likewise.
  if (!CollectUnpackedSliceElements(stmt->rhs, ctx, arena, src) || src.empty())
    FillSliceSourceFromPacked(stmt, dst, ctx, arena, src);
  WriteUnpackedSliceElements(dst, src, ctx, arena);
  return true;
}

static Variable* FindOrCreateElement(const std::string& name, uint32_t width,
                                     SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(name);
  if (var) return var;
  return ctx.CreateVariable(*arena.Create<std::string>(name), width);
}

static bool IsCompoundSelect(const Expr* expr) {
  return expr && expr->kind == ExprKind::kSelect && expr->base &&
         expr->base->kind == ExprKind::kSelect && !expr->index_end;
}

static bool TrySubarrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!IsCompoundSelect(stmt->lhs) || !IsCompoundSelect(stmt->rhs))
    return false;
  std::string dst_prefix, src_prefix;
  if (!BuildCompoundLhsName(stmt->lhs, ctx, arena, dst_prefix)) return false;
  if (!BuildCompoundLhsName(stmt->rhs, ctx, arena, src_prefix)) return false;
  std::string match = src_prefix + "[";
  std::vector<std::pair<std::string, Logic4Vec>> elems;
  // Each element of the source subarray is a storage element of its own under
  // §6.8, so the run is copied where it is gathered rather than shared with
  // the destination's elements. This handler runs ahead of the right-hand
  // value the statement executor makes and gathers its own, so none of that
  // value's copy reaches here; and the store below neither resizes nor
  // coerces, so `b = a` was quiet where it paired the elements up and the
  // shared words only showed on the next write to either array.
  for (const auto& [vname, vptr] : ctx.GetVariables()) {
    if (vname.starts_with(match))
      elems.emplace_back(std::string(vname.substr(src_prefix.size())),
                         OwnRhsWords(vptr->value, arena));
  }
  if (elems.empty()) return false;
  for (const auto& [suffix, val] : elems) {
    auto* dst = FindOrCreateElement(dst_prefix + suffix, val.width, ctx, arena);
    dst->value = val;
    dst->NotifyWatchers();
  }
  return true;
}

// §11.5.1: how wide a select is as an expression. A bit-select extracts "a
// particular bit from a vector, packed array, packed structure, parameter, or
// concatenation", so it is one bit -- or, where one index of a packed
// multidimensional array addresses an element rather than a bit (§7.4.1), that
// element. A part-select addresses "several contiguous bits": "the number of
// bits selected is equal to the width expression" for an indexed one and the
// span of its two constant indices for a non-indexed one, which is the same
// number read off the pair PartSelectTargetIndices resolves for all three
// forms. §11.6.1's Table 11-21 sizes no select, so these widths are §11.5.1's.
//
// An address outside the declared bounds changes none of it: §11.5.1 gives the
// invalid reference a value rather than an absence -- "the value returned by
// the reference shall be x for 4-state and 0 for 2-state values" -- and says
// separately that such a write "shall have no effect on the data stored".
//
// Zero is answered where the select names no bits: a part-select whose bounds
// or width expression carry x or z, and an indexed one whose width is zero. An
// unknown base index leaves an indexed part-select its stated width, §11.5.1
// letting that base "vary at run time", and a bit-select whose index carries x
// or z is one bit like any other, that clause covering the out-of-bounds
// address and the unknown one in one sentence.
//
// §11.4.14.1 asks the same question of a streaming-concatenation target
// element, each stream_expression being "converted to a bit-stream and
// appended", so this is declared in statement_assign_internal.h and the
// streaming unpack shares it rather than restating these four shapes.
uint32_t SelectExprWidth(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena) {
  if (sel->index_end == nullptr)
    return var.packed_elem_width > 1 ? var.packed_elem_width : 1;
  bool is_indexed = sel->is_part_select_plus || sel->is_part_select_minus;
  auto idx_val = EvalExpr(sel->index, ctx, arena);
  auto end_val = EvalExpr(sel->index_end, ctx, arena);
  if (HasUnknownBits(end_val)) return 0;
  if (!is_indexed && HasUnknownBits(idx_val)) return 0;
  // §5.7.1 makes a bare decimal a signed integer and §11.5.1 asks for "constant
  // integer expressions" as the bounds, so a negative one is read through
  // SelectBoundValue rather than cast from ToUint64. The window this width is
  // paired with reads it the same way, and the two have to agree: sized here
  // from an unsigned 4294967294 and written from a signed -2, an element would
  // claim a different number of bits from the one it writes into.
  auto target = PartSelectTargetIndices(
      SelectBoundValue(idx_val), SelectBoundValue(end_val),
      sel->is_part_select_plus, sel->is_part_select_minus);
  // §11.5.1 requires an indexed part-select's width to "be a positive
  // constant", so a zero one names no bit and the select is no bits wide. This
  // and SelectStorageBits answer one question off one struct, and only that one
  // read its third field: the pair below is the two ends of a width the select
  // does not have -- 3 and 2 for `a[3 +: 0]` -- so `{a[3 +: 0], b}` claimed two
  // bits of the value and wrote none of them.
  if (target.declared_width == 0) return 0;
  return static_cast<uint32_t>(std::max(target.first, target.second) -
                               std::min(target.first, target.second) + 1);
}

// §11.4.12/§11.5.1: width of a concatenation lvalue element -- a nested
// concatenation/assignment pattern sums its own elements, a select is as wide
// as SelectExprWidth makes it, and any other form reduces to the width of the
// resolved target variable. Zero is the element this cannot size at all, which
// a caller passes over without advancing its offset, having no width to
// advance by.
//
// How wide the element is and which bits of its object it may write are two
// questions, and this answers the first. Answering the second to both --
// SelectStorageBits' window, which is zero for a select addressing no bit --
// dropped such an element out of the concatenation entirely: on
// `logic [7:0] a, b, c`, `{c, a[9], b} = 17'h1AAC3` gave `a[9]` none of the
// seventeen bits, so `c` read 8'hAA where it owns bits [16:9] and must read
// 8'hD5. Reading the resolved variable's width for a select is the other way to
// draw the boundary wrong: `{a[3:0], b}` sized its first element at the whole
// of `a`. The writers ask SelectStorageBits for the window themselves, and
// ConcatLhsElemHasWritableBits below decides whether they write at all.
// Whether an index of `base` names a whole element rather than bits within a
// packed object. §7.4.2's fixed unpacked array is registered as an ArrayInfo;
// §7.10's queue and §7.8's associative array are not registered as one at all,
// their elements living in a QueueObject and an AssocArrayObject, so asking
// FindArrayInfo alone answered no for them and a select of one was measured as
// a bit-select of the variable the lowerer creates under the name -- a variable
// that models one element, so `qu[0]` came back one bit wide. That width is
// §11.6.1's context for the operation and, since #3502, §11.3.6's type for the
// value an assignment expression yields, so both were sized to a bit.
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
  if (var == nullptr) return 0;
  // Two questions, not one. SelectExprWidth answers how many bits a select
  // names within a packed object; an index of a collection names a whole
  // element, whose width is the base variable's, itself one element wide.
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      !IndexNamesWholeElement(LhsIdentName(e->base), ctx)) {
    return SelectExprWidth(*var, e, ctx, arena);
  }
  return var->value.width;
}

// §11.5.1: whether the concatenation lvalue element `e`, having resolved to
// `var`, addresses any bit of it. A select whose address lies wholly outside
// the declared bounds or carries x or z addresses none, that write having "no
// effect on the data stored"; every other element shape names the whole of the
// variable it resolved to.
//
// This is the second of the two questions ConcatLhsElemWidth used to answer as
// well as the first, and it is asked on its own because an element that writes
// nothing has to leave everything else about its target alone too: the blocking
// path would otherwise wake the target's watchers for a change §9.4.2 never
// saw, and the §10.6 path would mark the whole variable forced.
bool ConcatLhsElemHasWritableBits(const Expr* e, const Variable& var,
                                  SimContext& ctx, Arena& arena) {
  if (e->kind != ExprKind::kSelect || e->base == nullptr) return true;
  return SelectStorageBits(var, e, ctx, arena).width > 0;
}

// Deposits one non-nested element of a concatenation lvalue its slice. The
// element has already taken its own width of the right-hand value, which is
// what it names; what it writes is a narrower thing whenever a select runs off
// the end of its object.
static void WriteConcatLhsElement(const Expr* el, const Logic4Vec& slice,
                                  SimContext& ctx, Arena& arena) {
  // §7.4.2 makes `out[i]` on an unpacked array a reference to one whole
  // element, and §11.4.12 gives a concatenation element the bits its own width
  // claims -- ConcatLhsElemWidth having already sized this one by the element's
  // width. These are the three writers TrySelectBlockingAssign asks first for a
  // lone target, in its order, and asking none of them is what sent an element
  // to ResolveLhsVariable below: that answers the variable the lowerer creates
  // under the array's own name, one element wide and read by nothing, so the
  // slice was deposited one bit at a time into a carrier and lost -- `{out[1],
  // b} = 16'hABCD` left out[1] holding what it held while `b` took 8'hCD.
  if (auto* elem = TryResolveArrayElement(el, ctx)) {
    WriteVar(elem, slice, arena);
    return;
  }
  if (TryQueueIndexedWrite(el, slice, ctx, arena)) return;
  if (TryAssocIndexedWrite(el, slice, ctx, arena)) return;
  auto* var = ResolveLhsVariable(el, ctx);
  if (var == nullptr) return;
  // A select element takes the bits it named and leaves the rest of its
  // variable standing; writing the variable whole gave `{a[3:0], b}` all of
  // `a`. WriteBitSelect resolves the window §11.5.1 gives the indices.
  if (el->kind == ExprKind::kSelect && el->base != nullptr) {
    // §11.5.1: a select addressing no bit of its object "shall have no effect
    // on the data stored when written", so this element writes nothing and
    // wakes nobody -- WriteBitSelect declines the write and, since #3522, the
    // notification with it, §9.4.2 detecting a change rather than an attempt at
    // one. The check stays ahead of the writer all the same: a concatenation
    // element that names no bit is passed over silently, where WriteBitSelect
    // reports the zero-width part-select form of it as an error.
    if (!ConcatLhsElemHasWritableBits(el, *var, ctx, arena)) return;
    WriteBitSelect(var, el, slice, ctx, arena);
    return;
  }
  // §10.6.2's override reaches an element by its own whole-variable write, and
  // this arm runs before any writer carrying the rule is consulted. The select
  // element above is WriteBitSelect's to decline.
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
      // §11.5.1 requires an indexed part-select's width to "be a positive
      // constant", so an element written with a width of zero is illegal
      // rather than merely empty and is reported before being passed over.
      // The report gates itself on the select carrying such a width, so the
      // other causes of a zero here -- an element this cannot size at all, a
      // part-select whose bounds carry x or z -- stay silent, as they were.
      ReportZeroWidthPartSelect(el, ctx, arena);
      continue;
    }
    // §11.4.1 gives each element the bits its own width claims, and nothing in
    // the clause bounds a concatenation at one word or drops the x and z bits
    // of what is assigned. Taking the slice with ExtractBitField rather than
    // through Logic4Vec::ToUint64 keeps both: that reads words[0] alone and
    // returns `aval & ~bval`, so a concatenation wider than 64 bits lost
    // everything above bit 63 and an x or a z arrived as 0.
    Logic4Vec slice = ExtractBitField(arena, rhs_val, bit_offset, w);
    bit_offset += w;
    // §11.4.1: a nested concatenation lvalue distributes its slice recursively.
    if (el->kind == ExprKind::kConcatenation ||
        el->kind == ExprKind::kAssignmentPattern) {
      UnpackConcatLhs(el, slice, ctx, arena);
      continue;
    }
    WriteConcatLhsElement(el, slice, ctx, arena);
  }
}

// §11.4.12: "The concatenation is treated as a packed vector of bits. It can be
// used on the left-hand side of an assignment", and §10.9 gives a typed or bare
// assignment pattern the same use, so both distribute the value across their
// elements rather than naming one object to receive it. Answers whether the
// left-hand side was one of those, so that a caller with its own statement
// executor asks the question once rather than restating which shapes count.
bool TryUnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena) {
  if (!IsConcatLhs(lhs)) return false;
  UnpackConcatLhs(UnwrapTypedPattern(lhs), rhs_val, ctx, arena);
  return true;
}

static Logic4Vec ConvertToRealIfNeeded(double d, uint32_t target_width,
                                       Arena& arena) {
  if (target_width == 32) {
    auto f = static_cast<float>(d);
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    auto result = MakeLogic4VecVal(arena, 32, fbits);
    result.is_real = true;
    return result;
  }
  uint64_t dbits = 0;
  std::memcpy(&dbits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, 64, dbits);
  result.is_real = true;
  return result;
}

Logic4Vec ConvertRealForKnownLhs(Logic4Vec rhs_val, bool lhs_is_real,
                                 uint32_t target_width, Arena& arena) {
  // §6.12.1: a real assigned to an integer converts by rounding to the nearest
  // integer with ties away from zero (std::llround), never a raw bit copy.
  if (rhs_val.is_real && !lhs_is_real) {
    double d = RealVecToDouble(rhs_val);
    auto ival = static_cast<uint64_t>(static_cast<int64_t>(std::llround(d)));
    auto result = MakeLogic4VecVal(arena, target_width, ival);
    result.is_signed = true;
    return result;
  }
  // §6.12.1: an expression assigned to a real converts numerically; x/z bits of
  // the source read as zero (ToUint64's aval & ~bval projection).
  if (!rhs_val.is_real && lhs_is_real) {
    uint64_t raw = rhs_val.nwords > 0
                       ? (rhs_val.words[0].aval & ~rhs_val.words[0].bval)
                       : 0;
    auto d = static_cast<double>(raw);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  if (rhs_val.is_real && lhs_is_real && rhs_val.width != target_width) {
    double d = RealVecToDouble(rhs_val);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  return ResizeToWidth(rhs_val, target_width, arena);
}

Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              uint32_t target_width, SimContext& ctx,
                              Arena& arena) {
  auto name = LhsIdentName(lhs);
  if (name.empty()) return ResizeToWidth(rhs_val, target_width, arena);
  bool lhs_is_real = ctx.IsRealVariable(name);
  return ConvertRealForKnownLhs(rhs_val, lhs_is_real, target_width, arena);
}

static void AssignToScalarLhs(const Stmt* stmt, Logic4Vec rhs_val,
                              SimContext& ctx, Arena& arena) {
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (var) {
    if (var->is_forced) return;

    auto lhs_name = LhsIdentName(stmt->lhs);
    if (!lhs_name.empty() && ctx.IsStringVariable(lhs_name)) {
      var->value = StripStringZeros(rhs_val, arena);
      var->NotifyWatchers();
      return;
    }
    rhs_val =
        ConvertRealOnAssign(rhs_val, stmt->lhs, var->value.width, ctx, arena);
    var->value = rhs_val;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();

    if (stmt->rhs && stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs)
      ctx.SetVariableTag(stmt->lhs->text, stmt->rhs->rhs->text);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(stmt->lhs, rhs_val, ctx);
  }
}

// §25.9: assignment to a virtual interface variable. The right-hand side is
// another virtual interface, an interface instance, or null; bind, copy, or
// clear the target's interface-instance binding accordingly.
static bool TryVirtualInterfaceAssign(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
  if (!ctx.IsVirtualInterfaceVar(lhs_var)) return false;
  const Expr* rhs = stmt->rhs;
  if (!rhs || rhs->kind != ExprKind::kIdentifier) return false;

  if (rhs->text == "null") {
    ctx.UnbindVirtualInterface(lhs_var);
    return true;
  }
  auto* rhs_var = ctx.FindVariable(rhs->text);
  if (ctx.IsVirtualInterfaceVar(rhs_var)) {
    if (ctx.VirtualInterfaceIsBound(rhs_var)) {
      std::string src(ctx.VirtualInterfaceBinding(rhs_var));
      ctx.BindVirtualInterface(lhs_var, src);
    } else {
      ctx.UnbindVirtualInterface(lhs_var);
    }
    return true;
  }
  std::string scope = ctx.ResolveInstanceScope(rhs->text);
  if (!scope.empty()) {
    ctx.BindVirtualInterface(lhs_var, scope);
    return true;
  }
  return false;
}

// §6.18: assignment between named event variables. `e = null` nullifies the
// event; `e1 = e2` (both events) aliases the lhs to the rhs trigger.
static bool TryEventVarAssign(const Stmt* stmt, SimContext& ctx) {
  if (stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs ||
      stmt->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
  if (!lhs_var || !lhs_var->is_event) return false;

  if (stmt->rhs->text == "null") {
    ctx.NullifyEventVariable(stmt->lhs->text);
    return true;
  }
  auto* rhs_var = ctx.FindVariable(stmt->rhs->text);
  if (rhs_var && rhs_var->is_event) {
    ctx.AliasVariable(stmt->lhs->text, stmt->rhs->text);
    return true;
  }
  return false;
}

// §11.4.1: a compound assignment evaluates any left-hand index expression only
// once. The resolve/read/write helpers below each re-derive the target from
// lhs->index (and index_end) by calling EvalExpr on those nodes, which would
// invoke a side-effecting index (e.g. `data[f()] += 1`) several times. Evaluate
// each index expression a single time up front and stash the result as a
// per-expression snapshot; EvalExpr returns a stored snapshot ahead of any real
// evaluation, so every later read of the same index node reuses this value.
void SnapshotSelectIndices(const Expr* lhs, SimContext& ctx, Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  SnapshotSelectIndices(lhs->base, ctx, arena);
  if (lhs->index != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index, EvalExpr(lhs->index, ctx, arena));
  if (lhs->index_end != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index_end,
                               EvalExpr(lhs->index_end, ctx, arena));
}

// Undoes SnapshotSelectIndices once the compound assignment has finished so the
// snapshots do not leak into later statements that reuse the same index nodes.
void ClearSelectIndices(const Expr* lhs, SimContext& ctx) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  ClearSelectIndices(lhs->base, ctx);
  if (lhs->index != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index);
  if (lhs->index_end != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index_end);
}

void ApplyCompoundAssignOp(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto base_op = CompoundAssignBaseOp(stmt->rhs->op);
  auto actual_rhs = EvalExpr(stmt->rhs->rhs, ctx, arena);

  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ResolveLhsVariable(stmt->lhs, ctx);
    if (var) {
      auto result = EvalBinaryOp(base_op, var->value, actual_rhs, arena);
      // §6.12.1's conversion, which WriteVar does not apply: `int i; i += 1.5;`
      // computes a real and stores an integer.
      result =
          ConvertRealOnAssign(result, stmt->lhs, var->value.width, ctx, arena);
      WriteVar(var, result, arena);
    }
  } else if (stmt->lhs->kind == ExprKind::kSelect) {
    SnapshotSelectIndices(stmt->lhs, ctx, arena);
    if (auto* elem = TryResolveArrayElement(stmt->lhs, ctx)) {
      auto result = EvalBinaryOp(base_op, elem->value, actual_rhs, arena);
      WriteVar(elem, result, arena);
    } else {
      // §7.8.7: a compound assignment reads and writes in one statement, so a
      // nonexistent associative array element is allocated with its initial
      // value before the read below rather than by the write after it.
      AllocateAssocEntryForModify(stmt->lhs, ctx, arena);
      auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
      auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
      TrySelectBlockingAssign(stmt->lhs, result, ctx, arena);
    }
    ClearSelectIndices(stmt->lhs, ctx);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
    auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
    WriteStructField(stmt->lhs, result, ctx);
  } else {
    auto result = EvalExpr(stmt->rhs, ctx, arena);
    AssignToScalarLhs(stmt, result, ctx, arena);
  }
}

// Run the chain of special-case blocking-assignment handlers that do not need
// the generic rhs value (virtual interfaces, class `new`, associative-array
// copy/literal, streaming-to-queue, queue/event/slice/subarray, and compound
// operators). Returns true when one of them fully handled the assignment.
static bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                             Arena& arena) {
  if (TryVirtualInterfaceAssign(stmt, ctx)) return true;
  if (TrySemaphoreNewAssign(stmt, ctx, arena)) return true;
  if (TryClassNewAssign(stmt, ctx, arena)) return true;
  if (TryTypedClassNewAssign(stmt, ctx, arena)) return true;
  if (TryMemberClassNewAssign(stmt, ctx, arena)) return true;
  if (TryAssocMapAssign(stmt, ctx, arena)) return true;
  if (TryAssocCopyAssign(stmt, ctx)) return true;
  if (TryAssocLiteralAssign(stmt, ctx, arena)) return true;
  if (TryStreamingConcatToQueueTarget(stmt, ctx, arena)) return true;
  if (TryQueueBlockingAssign(stmt, ctx, arena)) return true;
  if (TryEventVarAssign(stmt, ctx)) return true;
  if (TryUnpackedSliceAssign(stmt, ctx, arena)) return true;
  if (TrySubarrayAssign(stmt, ctx, arena)) return true;
  // A bare `lhs op= rhs` statement carries the compound operator as its own rhs
  // node. A parenthesized compound assign is instead an embedded assignment
  // expression (11.4.1 primary `( operator_assignment )`), e.g. `x = (y += 2)`,
  // whose target is its own lhs (y), not the statement lhs (x); let it fall
  // through to the generic path so EvalExpr routes it to EvalCompoundAssign.
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(stmt->rhs->op) && !stmt->rhs->is_parenthesized) {
    ApplyCompoundAssignOp(stmt, ctx, arena);
    return true;
  }
  return false;
}

// Apply the generic blocking assignment of `rhs_val` once the special-case
// handlers have declined. Covers concatenation/pattern unpack, streaming
// unpack, bit/part-select writes, array writes, and the scalar fallback.
static void ApplyGenericBlockingAssign(const Stmt* stmt, Logic4Vec rhs_val,
                                       SimContext& ctx, Arena& arena) {
  // §10.9: a typed assignment pattern expression (type'{...}) is also a valid
  // left-hand target, and TryUnpackConcatLhs strips the type prefix so its
  // members unpack the RHS exactly as a bare positional pattern does.
  if (TryUnpackConcatLhs(stmt->lhs, rhs_val, ctx, arena)) return;
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  rhs_val = ApplyStreamPackToTargetWidening(stmt, rhs_val, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  if (TryArrayBlockingAssign(stmt, ctx, arena)) return;
  AssignToScalarLhs(stmt, rhs_val, ctx, arena);
}

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  if (TryDispatchSpecialBlockingAssign(stmt, ctx, arena))
    return StmtResult::kDone;
  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);
  // Every generic blocking store -- the scalar write, the select writers,
  // WriteStructField and the class property behind it -- takes the value from
  // here, so one copy at the point it is produced covers all of them.
  rhs_val = OwnRhsWords(rhs_val, arena);
  ApplyGenericBlockingAssign(stmt, rhs_val, ctx, arena);
  return StmtResult::kDone;
}

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena) {
  if (!lhs) return;
  // The value arrives already made, from a caller outside this file -- an
  // embedded assignment expression, a continuous assignment's driven value, an
  // output argument's writeback, a DPI or system task's result. This entry is
  // where such a value is produced as far as the store path can see, so it is
  // copied once here rather than in the arms below.
  Logic4Vec owned = OwnRhsWords(rhs_val, arena);
  // §10.9: a typed assignment pattern expression on the left unpacks like the
  // bare pattern it wraps.
  if (IsConcatLhs(lhs)) {
    UnpackConcatLhs(UnwrapTypedPattern(lhs), owned, ctx, arena);
    return;
  }

  if (lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(lhs, owned, ctx, arena);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(lhs, owned, ctx, arena);
    return;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (var) {
    if (var->is_forced) return;
    auto converted =
        ConvertRealOnAssign(owned, lhs, var->value.width, ctx, arena);
    var->value = converted;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  } else if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, owned, ctx);
  }
}

}  // namespace delta
