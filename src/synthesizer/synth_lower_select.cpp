#include <algorithm>
#include <cstdint>
#include <optional>
#include <string_view>

#include "elaborator/elaborator_helpers.h"
#include "synthesizer/synth_lower.h"

namespace delta {

// The number of bit positions a select's index is compared over where it did
// not fold. The comparison has to reject every value the index can carry that
// names no bit of the base, and reading the index at fewer positions than it
// can carry would let such a value match a candidate on the positions read.
// SynthLower::LowerExprBit answers constant false above an operand's own width
// and AigGraph::AddAnd folds a constant, so the positions above the index cost
// no gate.
static constexpr uint32_t kSelectIndexBits = 32;

DeclaredPackedRange SynthLower::BaseRange(const Expr* base) {
  if (!base || base->kind != ExprKind::kIdentifier) {
    return DeclaredPackedRange::Implicit(0);
  }
  auto it = signal_ranges_.find(base->text);
  if (it != signal_ranges_.end()) return it->second;
  return DeclaredPackedRange::Implicit(SignalWidth(base->text));
}

bool SynthLower::IsVectorSelect(const Expr* sel) {
  if (!sel || !sel->base || sel->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  return unpacked_arrays_.count(sel->base->text) == 0;
}

SynthLower::SelectStorage SynthLower::ResolveSelect(const Expr* sel) {
  if (!IsVectorSelect(sel)) return {};
  std::optional<int64_t> index = ConstEvalInt(sel->index, scope_);
  if (!index) return {};

  // §11.5.1 defines three forms over one pair of operands. A bit-select names
  // one index. A non-indexed part-select `vect[msb_expr:lsb_expr]` names the
  // two ends themselves. An indexed part-select names a base and a width, and
  // covers `width` indices from that base: `[base +: width]` ascends the bit
  // range and `[base -: width]` descends it, which the subclause states with
  // `a_vect[0 +: 8]` reading as `a_vect[7:0]` and `a_vect[15 -: 8]` as
  // `a_vect[15:8]`.
  int64_t first = *index;
  int64_t second = *index;
  if (sel->index_end) {
    std::optional<int64_t> end = ConstEvalInt(sel->index_end, scope_);
    if (!end) return {};
    if (sel->is_part_select_plus) {
      second = first + *end - 1;
    } else if (sel->is_part_select_minus) {
      second = first - *end + 1;
    } else {
      second = *end;
    }
  }

  // §11.5.1: "The actual bit that is accessed by an address is, in part,
  // determined by the declaration", so each end is resolved against the range
  // the base was declared with rather than counted from the bottom of its
  // storage. The two ends give a run of contiguous offsets whichever way that
  // declaration runs, and the lower of the two is where the run starts.
  DeclaredPackedRange range = BaseRange(sel->base);
  int64_t first_offset = range.OffsetOfIndex(first);
  int64_t second_offset = range.OffsetOfIndex(second);
  int64_t lo = std::min(first_offset, second_offset);
  int64_t hi = std::max(first_offset, second_offset);
  return {sel->base->text, lo, static_cast<uint32_t>(hi - lo + 1)};
}

uint32_t SynthLower::ExprEqualsValue(const Expr* expr, AigGraph& aig,
                                     int64_t value) {
  uint32_t match = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < kSelectIndexBits; ++b) {
    uint32_t want = ((static_cast<uint64_t>(value) >> b) & 1u) != 0
                        ? AigGraph::kConstTrue
                        : AigGraph::kConstFalse;
    uint32_t have = LowerExprBit(expr, aig, b);
    match = aig.AddAnd(match, aig.AddNot(aig.AddXor(have, want)));
  }
  return match;
}

int64_t SynthLower::VariableSelectWidth(const Expr* expr) {
  // §11.5.1 rules that the width of an indexed part-select "shall be a
  // positive constant integer expression", so a width that does not fold is
  // not a select this builds anything for. A non-indexed part-select is
  // written with two constant expressions and reaches this function only when
  // one of them did not fold, which is the same case.
  if (!expr->index_end) return 1;
  if (!expr->is_part_select_plus && !expr->is_part_select_minus) return 0;
  std::optional<int64_t> end = ConstEvalInt(expr->index_end, scope_);
  if (!end || *end <= 0) return 0;
  return *end;
}

int64_t SynthLower::VariableSelectIndex(const Expr* expr, int64_t value,
                                        int64_t width, uint32_t bit) {
  // §11.5.1: `[base +: width]` covers the indices `base` through
  // `base + width - 1`, and `[base -: width]` covers `base - width + 1`
  // through `base`. A bit-select covers the one index its expression carries.
  if (expr->is_part_select_plus) return value + static_cast<int64_t>(bit);
  if (expr->is_part_select_minus) {
    return value - width + 1 + static_cast<int64_t>(bit);
  }
  return value;
}

uint32_t SynthLower::LowerVariableSelectBit(const Expr* expr, AigGraph& aig,
                                            uint32_t bit) {
  if (!IsVectorSelect(expr)) return AigGraph::kConstFalse;
  int64_t width = VariableSelectWidth(expr);
  if (width == 0 || static_cast<int64_t>(bit) >= width) {
    return AigGraph::kConstFalse;
  }

  // The select chooses among the bits of its base under the value the index
  // carries, so the netlist owes a multiplexer over the values that name a bit
  // of it. Each candidate is one value the index can take; the base is read at
  // the offset that value resolves to, and a value the index can carry that
  // matches no candidate leaves the answer at constant false, which is what
  // §11.5.1 returns for an address that is out of bounds of a 2-state value.
  DeclaredPackedRange range = BaseRange(expr->base);
  uint32_t base_width = SignalWidth(expr->base->text);
  int64_t high = std::max(range.left, range.right);
  uint32_t result = AigGraph::kConstFalse;
  for (int64_t value = 0; value <= high + width - 1; ++value) {
    int64_t offset =
        range.OffsetOfIndex(VariableSelectIndex(expr, value, width, bit));
    if (offset < 0 || offset >= static_cast<int64_t>(base_width)) continue;
    uint32_t source =
        GetSignalBit(expr->base->text, static_cast<uint32_t>(offset));
    result =
        aig.AddMux(ExprEqualsValue(expr->index, aig, value), source, result);
  }
  return result;
}

uint32_t SynthLower::LowerSelectBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  SelectStorage storage = ResolveSelect(expr);
  if (storage.count == 0) return LowerVariableSelectBit(expr, aig, bit);
  if (bit >= storage.count) return AigGraph::kConstFalse;

  // §11.5.1: a part-select "partially out of range shall, when read, return x
  // for the bits that are out of range", and a 2-state value reads 0 where a
  // 4-state one reads x. An AIG node holds two values, so constant false is
  // that answer, and SynthLower::GetSignalBit already gives it above the
  // signal's width.
  int64_t offset = storage.lo + bit;
  if (offset < 0) return AigGraph::kConstFalse;
  return GetSignalBit(storage.name, static_cast<uint32_t>(offset));
}

void SynthLower::LowerSelectTarget(const Expr* lhs, const Expr* rhs,
                                   AigGraph& aig) {
  SelectStorage storage = ResolveSelect(lhs);
  if (storage.count == 0) {
    // The select addresses no run of bits this can name: its base is not a
    // signal, or §11.5.2 addresses an element of an unpacked array, or an index
    // of it did not fold. §11.5.1 defines the bit-select addressed by an
    // expression and SynthLower::LowerVariableSelectBit builds it on the right
    // of an assignment, so a target of that form is a lowering this does not
    // have rather than a rule the design broke.
    ReportUnloweredTarget(lhs);
    return;
  }

  // §11.8.2: the size of the target propagates back down to the
  // context-determined operands of the right-hand side, and the target here is
  // the select rather than the whole signal, so it is the number of bits the
  // select addresses that propagates.
  propagated_width_ = storage.count;
  propagated_signed_ = IsSignedExpr(rhs);
  for (uint32_t b = 0; b < storage.count; ++b) {
    int64_t offset = storage.lo + static_cast<int64_t>(b);
    if (offset < 0) continue;
    SetSignalBit(storage.name, static_cast<uint32_t>(offset),
                 LowerAssignRhsBit(rhs, aig, b));
  }
  propagated_width_ = 0;
  propagated_signed_ = false;
}

void SynthLower::SetGenScope(const GenBlockConsts& consts) {
  scope_ = param_scope_;
  for (const auto& [name, value] : consts) {
    scope_[name] = value;
  }
}

}  // namespace delta
