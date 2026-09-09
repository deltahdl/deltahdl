#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §11.5.1's writes: what a bit-select or part-select of a variable deposits,
// and §10.7's resize, which is the step every one of them takes before the
// deposit. They sit apart from the member-path resolution in
// statement_assign.cpp because the question is a different one: that file
// answers which storage a name reaches, and this one answers what lands in a
// window of storage already found.

// Deposits `rhs_val` in the window of `var` that `bits` names. §11.5.1 has a
// part-select that is partly out of range "when written, only affect the bits
// that are in range", and which bits of the value the affected ones receive is
// bits.src_lo: a select running off the low end of its object has its own low
// bits land nowhere, so `a[1 -: 4] = 4'b1101` on a `logic [7:0] a` -- which the
// clause reads as `a[1:-2]` -- gives `a[1:0]` the value's bits [3:2] and must
// leave `a` at 8'h03. Taking the value's low bits whichever end the select ran
// off left it at 8'h01. The offset is zero for a select running off the high
// end, where the bits that land are the value's least significant ones.
//
// The window is deposited rather than computed in a machine word, because
// "only affect the bits that are in range" is a statement about every bit of
// the target the select did not name and not only about the ones beside it.
// Reading the target through Logic4Vec::ToUint64 and rebuilding it with
// MakeLogic4VecVal moved three sets of them. ToUint64 returns words[0] alone
// and MakeLogic4VecVal fills a fresh zeroed array, so a target wider than one
// word lost everything above bit 63: `w = '1; w[3:0] = 4'h0;` on a
// `logic [99:0] w` must leave 96 ones and left 60, w[99:64] being neither named
// by the select nor the value's to touch. ToUint64 returns `aval & ~bval` and
// MakeLogic4VecVal sets no bval, so the x and z that §6.3.1 lets every bit of a
// 4-state vector hold -- "All bits of 4-state vectors can be independently set
// to one of the four basic values", and §6.11.2 makes `logic` one of those
// types, whose values "have additional bits, which encode the x and z states"
// -- were read as 0 on the way in and stored as 0 on the way out:
// `a = 8'hxx; a[1:0] = 2'b11;` must read 8'bxxxxxx11 and read 8'b00000011, and
// `a = 8'h00; a[1:0] = 2'b1x;` must read 8'b0000001x and read 8'b00000010. And
// `mask << bits.lo` was undefined once the window began at bit 64 or above, the
// shift count being taken modulo 64 on x86-64, so `w[71:68] = 4'hF` on the same
// `logic [99:0] w` landed on w[7:4] and left w[71:68] at zero. DepositBitField
// is documented multi-word safe for a start bit of 64 or more, which answers
// the shift and the lost high words at once, and ExtractBitField takes the
// value's landing bits with their 4-state encoding kept, which answers the
// projection on the source side and makes bits.src_lo simply where the extract
// begins.
//
// The deposit is made into a fresh copy of the target's current value rather
// than through the words it is holding, for the reason WriteOwnedBits
// (statement_assign_decl.cpp) gives: copying a Logic4Vec copies its `words`
// pointer rather than the words (common/types.h), so a variable last written
// whole from another object shares that object's storage and an in-place
// deposit would write these bits into whatever else is holding it.
//
// §6.11.2 makes `bit` and `int` 2-state types that "do not have unknown
// values", so a 2-state target is coerced here explicitly. MakeLogic4VecVal
// gave that for free by never setting a bval; now that the deposit carries x
// and z, an x reaching such a target would otherwise survive.
void WritePartSelect(Variable* var, const PartSelectBits& bits,
                     const Logic4Vec& rhs_val, Arena& arena) {
  Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
  DepositBitField(updated, bits.lo,
                  ExtractBitField(arena, rhs_val, bits.src_lo, bits.width),
                  bits.width);
  var->value = updated;
  if (!var->is_4state) CoerceTo2State(var->value);
}

PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena) {
  auto idx_val = EvalExpr(sel->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return {0, 0};
  auto idx = SelectBoundValue(idx_val);
  if (sel->index_end == nullptr) {
    // §7.4.1: a single index on a packed multidimensional array addresses an
    // outermost element -- the inner dimensions' width -- rather than one bit,
    // and addresses it whole or not at all, so the source offset stays zero.
    if (var.packed_elem_width > 1) {
      PackedRange elems = var.DeclaredRange();
      if (!elems.Contains(idx)) return {0, 0};
      auto base = static_cast<uint32_t>(elems.OffsetOf(idx));
      return {base * var.packed_elem_width, var.packed_elem_width};
    }
    PackedRange range = var.BitSelectRange();
    if (!range.Contains(idx)) return {0, 0};
    return {static_cast<uint32_t>(range.OffsetOf(idx)), 1};
  }
  auto end_val = EvalExpr(sel->index_end, ctx, arena);
  if (HasUnknownBits(end_val)) return {0, 0};
  auto target = PartSelectTargetIndices(idx, SelectBoundValue(end_val),
                                        sel->is_part_select_plus,
                                        sel->is_part_select_minus);
  // §11.5.1 spells an indexed part-select's width out separately and requires
  // that it "shall be a positive constant", so a width of zero names no bit of
  // the object -- which is what a zero width from this function already means.
  // The pair PartSelectTargetIndices answers cannot say so on its own: it is
  // the two ends of a width the select does not have, and for `a[3 +: 0]` it is
  // the indices 3 and 2, which any declaration holding them resolves to the
  // two-bit window a[3:2]. The write path reports that width as an error ahead
  // of this call, in ReportZeroWidthPartSelect below; every caller reads the
  // zero this returns as the absence it is.
  if (target.declared_width == 0) return {0, 0};
  return PartSelectStorageBits(var.BitSelectRange(), target.first,
                               target.second);
}

// Whether two stored values differ, which is what the notification in
// WriteBitSelect turns on. It is the comparison EventAwaiter::CheckEdge makes
// for a non-edge event (awaiters_event_control.h) and the one the VCD writer
// makes to decide a transition (eval_system_task_dump.cpp), written out again
// here rather than shared with either, so that this file's own answer to
// §9.4.2's "change in the result of the expression" needs nothing from theirs.
static bool StoredBitsDiffer(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return true;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return true;
  }
  return false;
}

// §11.5.1's report for a select written with a width of zero, which is the one
// answer the resolution below cannot give: SelectStorageBits returns an empty
// window for it, and returns the same empty window for an unknown index, an
// out-of-range index and a select landing on no bit of the object, all of which
// the clause leaves silent. The width belongs to the select as written rather
// than to the object it addresses -- §11.5.1 requires it to "be a positive
// constant" -- so it is read on its own, from a base of zero, which is the
// declared width PartSelectTargetIndices gives either indexed form whatever the
// base is. Only those two forms carry a width, so `a[7:0]` reads nothing twice.
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

// The write itself, which §11.5.1 states as two questions this file now answers
// once each. "The actual bit that is accessed by an address is, in part,
// determined by the declaration" is the resolution, and SelectStorageBits
// answers it; a part-select partly out of range "shall, when written, only
// affect the bits that are in range" is the deposit, and WritePartSelect
// answers that. This function walked the same four arms a second time with the
// write attached -- the shape a correction lands on one of and not the other,
// as #3532 records on the nonblocking path, and one copy-paste-test cannot see,
// the two walks being an early-returning writer against a value-returning
// resolver rather than duplicated text. The bit-select goes with them, being
// the one-bit case of that window rather than a write of its own: computed in a
// machine word instead, `uint64_t{1} << off` was undefined for a bit at 64 or
// above, and `enable[64] = 1'b1;` on a `logic [64:0] enable` set enable[0].
//
// The packed arm's write carried one test the resolver has no counterpart for,
// `off < var->value.width`, and it is dropped rather than moved into
// SelectStorageBits. RecordPackedRange (lowerer_register.cpp) records a
// declared range only once its span times the element width equals value.width,
// so an index that range contains has its element wholly inside the value, and
// where the two disagree there is no declared range at all, only the implicit
// [width-1:0] one. DepositBitField answers both, breaking at the first bit at
// or past dst.width -- that same "only affect the bits that are in range" -- so
// an element past the value deposits none of itself. Only a read needs the test
// (TryPackedElementSelect, eval_select.cpp), owing a value where a write that
// lands nowhere owes nothing.
//
// Nothing here says anything about the notification, which WriteBitSelect
// decides from the stored value once this returns.
static void WriteBitSelectBits(Variable* var, const Expr* lhs,
                               const Logic4Vec& rhs_val, SimContext& ctx,
                               Arena& arena) {
  ReportZeroWidthPartSelect(lhs, ctx, arena);
  PartSelectBits bits = SelectStorageBits(*var, lhs, ctx, arena);
  if (bits.width == 0) return;
  WritePartSelect(var, bits, rhs_val, arena);
}

// Writes the window of `var` that `lhs` names, and wakes `var`'s watchers when
// that write moved the value.
//
// The notification is made here rather than by the callers because each of the
// five call sites had to remember the rule for itself, and they did not agree:
// #3521 is the record of one forgetting the notification entirely, and #3522
// the record of the four that remembered it remembering it in a form too
// coarse -- an unconditional NotifyWatchers() after a call that returns having
// written nothing down six separate paths. §9.4.2 closes with "A change of
// value in any operand of the expression without a change in the result of the
// expression shall not be detected as an event", so a statement that stored no
// bit owes no event at all: §11.5.1 gives an out-of-range write "no effect on
// the data stored when written", yet `a[9] = 1'b1;` on a `logic [7:0] a` ran an
// `always_comb` block reading `a` a third time.
//
// This function is the only one holding both the value before the write and the
// value after it, and "a change in the result" can only be measured between
// those two. The baseline is a Logic4Snapshot rather than a Logic4Vec copy
// because a Logic4Vec copied from `value` shares `value`'s words -- the copy
// takes the `words` pointer (common/types.h) -- so the deposit below would
// write through the baseline as well, the two sides of the comparison would be
// one value, and no change would ever be seen. That is #3358, and it is why
// Variable::prev_value is a snapshot too.
//
// A bool returned by the writer would not have been enough. It says "I wrote",
// not "the value changed", and those part company: `a[3] = 1'b1;` on a bit
// already 1 takes a writing path all the way to the deposit and changes
// nothing, which §9.4.2's last sentence is precisely about.
//
// The comparison sits at the end rather than beside the deposit, because the
// deposit is not where the paths end: the window WriteBitSelectBits resolves is
// empty for an unknown index, an out-of-range index, a zero declared width and
// a select landing on no bit of the object, and it returns having written
// nothing down every one of them. Reading the stored value once, after the
// write, is blind to which path ran.
void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  // §10.6.2: a force "shall override a procedural assignment ... until a
  // release procedural statement is executed on the variable". Naming a
  // bit-select or a part-select as the target does not take the statement out
  // of that class -- the clause's own "shall not be a bit-select or a
  // part-select of a variable" restricts what may be forced, not what a force
  // overrides -- so this declines as every whole-variable writer does. It is
  // the one place the statement form, the compound form, the increment, the
  // expression forms and the subroutine-body form all pass through. It declines
  // ahead of the snapshot, as WriteVar (statement_assign_core.cpp) declines
  // ahead of its own notification: nothing is written, so there is nothing to
  // compare and nobody to wake.
  if (var->is_forced) return;
  Logic4Snapshot before;
  before.Capture(var->value);
  WriteBitSelectBits(var, lhs, rhs_val, ctx, arena);
  if (StoredBitsDiffer(before.Get(), var->value)) var->NotifyWatchers();
}

// Single-word resize for known (no x/z) values that fit in 64 bits, applying
// sign extension when the source is signed and being widened.
// Logic4Vec::is_signed carries the signedness §11.7 gives the value itself,
// which $signed and $unsigned set, so the result takes the flag from val
// instead of the false MakeLogic4VecVal leaves in place. ResizeToWidth sets
// that flag from val on its wide path, and a value resized here is stored
// beside those, so the two paths have to answer alike.
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

// Replicates the source MSB across the widened high bits of result when val is
// signed and being widened past its original width.
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

// Clears any bits above target_width in the final (partial) word of result.
static void MaskHighBits(uint32_t target_width, Logic4Vec& result) {
  uint32_t last_bit = target_width % 64;
  if (last_bit == 0) return;
  uint32_t last_word = (target_width - 1) / 64;
  uint64_t mask = (uint64_t{1} << last_bit) - 1;
  result.words[last_word].aval &= mask;
  result.words[last_word].bval &= mask;
}

Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena) {
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

void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                       std::string_view src_name, const ArrayInfo& src,
                       SimContext& ctx) {
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
      // §7.6 does a whole-array copy by "assigning each element of the
      // source array to the corresponding element of the target array", so
      // this store is an assignment in its own right, and §6.8 makes what it
      // assigns to "an abstraction of a data storage element" holding "a value
      // from one assignment to the next". The destination element therefore
      // takes a copy of the source's words rather than the pointer to them
      // that a plain Logic4Vec assignment would leave the two sharing. This is
      // the whole-array spelling `b = a;` of the copy the slice and subarray
      // forms already own their words on.
      dv->value = OwnRhsWords(sv->value, ctx.GetArena());
      dv->NotifyWatchers();
    }
  }
}

}  // namespace delta
