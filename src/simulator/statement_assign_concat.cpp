#include <algorithm>
#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §11.4.12's concatenation and §10.9's assignment pattern as the left-hand
// side of a blocking assignment: which targets count as one (IsConcatLhs,
// UnwrapTypedPattern), how wide the whole and each element is (§11.6.1,
// §11.5.1: LhsContextWidth, ConcatLhsElemWidth, SelectExprWidth), the
// right-hand side evaluated in that context (§10.7: EvalRhsWithStructContext)
// and the value cut into the elements (TryUnpackConcatLhs).

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
    const StructTypeInfo* sinfo = StructLayoutOfName(stmt->lhs->text, ctx);
    if (const StructTypeInfo* member =
            sinfo ? TaggedMemberLayout(*sinfo, stmt->rhs->rhs->text) : nullptr)
      return EvalStructPatternValue(stmt->rhs->lhs, member, ctx, arena);
  }
  auto* inner = UnwrapTypedPattern(stmt->rhs);
  // §10.9.2: both keyed and positional structure patterns are evaluated against
  // the target's member layout so each member expression is coerced to its
  // member's type; only route when the target is actually a struct. §23.9:
  // the target resolves within the running instance, so its layout is asked
  // for by the key that instance's storage was created under; asked by the
  // bare name, a pattern assigned inside a child instance found no layout and
  // was concatenated in written order instead of placed by member.
  if (inner->kind != ExprKind::kAssignmentPattern)
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  const StructTypeInfo* sinfo = StructLayoutOfName(stmt->lhs->text, ctx);
  if (!sinfo) return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  return EvalStructPatternValue(inner, sinfo, ctx, arena);
}

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
  // §7.4.1: one index of a packed multidimensional array names an element,
  // and an index on that select names an element of the next packed dimension
  // (§7.4.4), one bit at the innermost -- `x[1][3]` on a `logic [1:0][7:0] x`
  // is a bit, not the eight-bit `x[1]`, and `z[1][0]` on a
  // `logic [1:0][1:0][7:0] z` eight bits of the sixteen-bit `z[1]` -- so the
  // width is that of the dimension the select's depth within the variable
  // reaches, as SelectStorageBits resolves the window by the same depth.
  if (sel->index_end == nullptr) {
    auto level = var.PackedLevelAt(SelectDepthWithin(var, sel, ctx, arena));
    return level ? level->elem_width : 1;
  }
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

}  // namespace delta
