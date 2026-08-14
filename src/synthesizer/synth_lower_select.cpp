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

PackedRange SynthLower::BaseRange(const Expr* base) {
  if (!base || base->kind != ExprKind::kIdentifier) {
    return PackedRange::Implicit(0);
  }
  auto it = signal_ranges_.find(base->text);
  if (it != signal_ranges_.end()) return it->second;
  return PackedRange::Implicit(SignalWidth(base->text));
}

bool SynthLower::IsVectorSelect(const Expr* sel) {
  if (!sel || !sel->base || sel->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  return unpacked_arrays_.count(sel->base->text) == 0;
}

// The name a chain of selects is written on. §11.5.2 writes `mem[2][3]` as a
// select over a select, and the declaration that resolves either of them is the
// one the name at the bottom carries.
static const Expr* SelectRootName(const Expr* expr) {
  while (expr && expr->kind == ExprKind::kSelect) expr = expr->base;
  return expr;
}

bool SynthLower::RecordArrayShape(const RtlirVariable& var) {
  // §11.5.2 resolves an address against the bounds the declaration gives, so an
  // array this can address is one whose low bound reached RTLIR.
  // RtlirVariable::unpacked_dim_sizes is filled only for a declaration of more
  // than one dimension, and it carries no direction per dimension, so a
  // multidimensional array is not one of them.
  if (var.unpacked_size == 0 || !var.unpacked_dim_sizes.empty()) return false;
  array_shapes_[var.name] =
      ArrayShape{var.width, var.unpacked_lo, var.unpacked_size};
  return true;
}

const SynthLower::ArrayShape* SynthLower::ArrayShapeOf(const Expr* base) {
  if (!base || base->kind != ExprKind::kIdentifier) return nullptr;
  auto it = array_shapes_.find(base->text);
  return it == array_shapes_.end() ? nullptr : &it->second;
}

SynthLower::SelectStorage SynthLower::ResolveArraySelect(const Expr* sel) {
  const ArrayShape* shape = ArrayShapeOf(sel->base);
  if (!shape) return {};
  // §11.5.2 gives an address per dimension, so a range written where an address
  // belongs is not an address this addresses an element with.
  if (sel->index_end) return {};
  std::optional<int64_t> address = ConstEvalInt(sel->index, scope_);
  if (!address) return {};
  // An address outside the declared bounds names a run outside the storage,
  // which SynthLower::GetSignalBit answers as constant false and
  // SynthLower::SetSignalBit ignores. §11.5.2 sends an invalid address to
  // §7.4.5, and a 2-state value reads 0 where a 4-state one reads x.
  int64_t lo = (*address - shape->lo) * static_cast<int64_t>(shape->elem_width);
  return {sel->base->text, lo, shape->elem_width};
}

SynthLower::SelectStorage SynthLower::ResolveSelect(const Expr* sel) {
  if (!sel || !sel->base) return {};

  // §11.5.2: an address written on the name of an array selects an element.
  if (ArrayShapeOf(sel->base) != nullptr) return ResolveArraySelect(sel);

  // §11.5.2 rules that once the element is selected, "bit-selects and
  // part-selects shall be addressed in the same manner as net and variable
  // bit-selects and part-selects (see 11.5.1)", so a select over a select
  // applies §11.5.1 inside the run the inner one addresses.
  SelectStorage base_run;
  if (sel->base->kind == ExprKind::kSelect) {
    base_run = ResolveSelect(sel->base);
    if (base_run.count == 0) return {};
  } else {
    if (!IsVectorSelect(sel)) return {};
    base_run = {sel->base->text, 0, SignalWidth(sel->base->text)};
  }

  std::optional<int64_t> index = ConstEvalInt(sel->index, scope_);
  if (!index) return {};

  // §11.5.1 defines three forms over one pair of operands, and
  // PartSelectTargetIndices in src/common/packed_range.h answers which indices
  // each addresses. A bit-select names one index and carries no second operand
  // to hand it.
  int64_t first = *index;
  int64_t second = *index;
  if (sel->index_end) {
    std::optional<int64_t> end = ConstEvalInt(sel->index_end, scope_);
    if (!end) return {};
    PartSelectIndices indices = PartSelectTargetIndices(
        *index, *end, sel->is_part_select_plus, sel->is_part_select_minus);
    first = indices.first;
    second = indices.second;
  }

  // §11.5.1: "The actual bit that is accessed by an address is, in part,
  // determined by the declaration", so each end is resolved against the range
  // the base was declared with rather than counted from the bottom of its
  // storage. The two ends give a run of contiguous offsets whichever way that
  // declaration runs, and the lower of the two is where the run starts.
  PackedRange range = BaseRange(SelectRootName(sel->base));
  int64_t first_offset = range.OffsetOf(first);
  int64_t second_offset = range.OffsetOf(second);
  int64_t lo = std::min(first_offset, second_offset);
  int64_t hi = std::max(first_offset, second_offset);
  return {base_run.name, base_run.lo + lo, static_cast<uint32_t>(hi - lo + 1)};
}

uint32_t SynthLower::LowerArraySelectBit(const Expr* expr, AigGraph& aig,
                                         uint32_t bit) {
  const ArrayShape* shape = ArrayShapeOf(expr->base);
  if (!shape || expr->index_end) {
    // §11.5.2 addressing this cannot resolve: an array whose declaration
    // reached RTLIR without the low bound its addresses are counted from, which
    // is every array port and every array of more than one dimension, or a
    // range written where an address belongs.
    ReportExprUnlowered(expr,
                        "an element of this unpacked array has no lowering in "
                        "the synthesizer",
                        Subclause("11.5.2"));
    return AigGraph::kConstFalse;
  }
  if (bit >= shape->elem_width) return AigGraph::kConstFalse;

  // §11.5.2 rules that "The addr_expr can be any integer expression", so an
  // address that did not fold chooses among the elements and the netlist owes a
  // multiplexer over the addresses the declaration admits. An address matching
  // none of them leaves constant false, which is what §7.4.5 gives a 2-state
  // value for an address that is out of bounds.
  uint32_t result = AigGraph::kConstFalse;
  for (uint32_t element = 0; element < shape->count; ++element) {
    uint32_t source =
        GetSignalBit(expr->base->text, element * shape->elem_width + bit);
    result = aig.AddMux(ExprEqualsValue(expr->index, aig, shape->lo + element),
                        source, result);
  }
  return result;
}

bool SynthLower::LowerArrayTarget(const Expr* lhs, const Expr* rhs,
                                  AigGraph& aig) {
  const ArrayShape* shape = ArrayShapeOf(lhs->base);
  if (!shape || lhs->index_end) return false;

  // §11.5.2: the address names one element, so every other element keeps what
  // it held. Each element takes the right-hand side where the address selects
  // it and its own bit where it does not, which is the same multiplexer the
  // read side builds, written into the storage rather than read out of it.
  propagated_width_ = shape->elem_width;
  propagated_signed_ = IsSignedExpr(rhs);
  for (uint32_t element = 0; element < shape->count; ++element) {
    uint32_t selected = ExprEqualsValue(lhs->index, aig, shape->lo + element);
    for (uint32_t b = 0; b < shape->elem_width; ++b) {
      uint32_t offset = element * shape->elem_width + b;
      uint32_t held = GetSignalBit(lhs->base->text, offset);
      uint32_t driven = LowerAssignRhsBit(rhs, aig, b);
      SetSignalBit(lhs->base->text, offset, aig.AddMux(selected, driven, held));
    }
  }
  propagated_width_ = 0;
  propagated_signed_ = false;
  return true;
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
  // §11.5.1: an indexed part-select covers a contiguous run of indices, and
  // PartSelectTargetIndices in src/common/packed_range.h answers where that run
  // starts. Bit `bit` of the result is that many indices along it, ascending,
  // because the first of the pair is the numerically lower end for both `+:`
  // and `-:`.
  //
  // A non-indexed part-select does not reach here, since
  // SynthLower::VariableSelectWidth answers zero for one. That is what leaves
  // the first of the pair the lower end: for a non-indexed part-select it is
  // the more significant index instead.
  return PartSelectTargetIndices(value, width, expr->is_part_select_plus,
                                 expr->is_part_select_minus)
             .first +
         static_cast<int64_t>(bit);
}

uint32_t SynthLower::LowerVariableSelectBit(const Expr* expr, AigGraph& aig,
                                            uint32_t bit) {
  // §11.5.2 addresses an element of an unpacked array and §11.5.1 a bit of a
  // vector, and the two are written alike, so the declaration decides which
  // this is.
  if (!IsVectorSelect(expr)) return LowerArraySelectBit(expr, aig, bit);
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
  PackedRange range = BaseRange(expr->base);
  uint32_t base_width = SignalWidth(expr->base->text);
  int64_t high = std::max(range.left, range.right);
  uint32_t result = AigGraph::kConstFalse;
  for (int64_t value = 0; value <= high + width - 1; ++value) {
    int64_t offset =
        range.OffsetOf(VariableSelectIndex(expr, value, width, bit));
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
    // §11.5.2 admits an address that is any integer expression, so an address
    // on an array that did not fold drives one element under that address
    // rather than naming a run of bits.
    if (LowerArrayTarget(lhs, rhs, aig)) return;
    // The select addresses no run of bits this can name: its base is not a
    // signal, or an index of it did not fold. §11.5.1 defines the bit-select
    // addressed by an expression and SynthLower::LowerVariableSelectBit builds
    // it on the right of an assignment, so a target of that form is a lowering
    // this does not have rather than a rule the design broke.
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
