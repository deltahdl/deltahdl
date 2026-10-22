// §28.3.6: the terminals of an array of gate or switch instances, measured and
// shared out a bit per instance.

#include "elaborator/elaborator_gate_array_terminals.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"

namespace delta {

namespace {

// `base[index]`, the one bit an instance of the array connects to.
Expr* MakeBitSelectAt(Arena& arena, Expr* base, int64_t index) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = static_cast<uint64_t>(index);
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = lit;
  return e;
}

// §5.7.1: the literal of one bit whose 4-state encoding is `aval` and `bval`,
// 1'b0, 1'b1, 1'bz or 1'bx.
Expr* OneBitLiteral(Arena& arena, size_t aval, size_t bval) {
  static constexpr std::string_view kBitTexts[] = {"1'b0", "1'b1", "1'bz",
                                                   "1'bx"};
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = kBitTexts[(bval * 2) + aval];
  e->int_val = aval * (1 - bval);
  return e;
}

// §5.7.1: the bit `bit` above the least significant end of the integer
// literal `lit`, a 0, 1, x or z, as a literal of one bit of its own, the
// constant one instance of the array connects to.
Expr* LiteralBitAt(Arena& arena, const Expr* lit, uint32_t bit) {
  const Logic4Vec kValue = EvalIntLiteral(lit, arena);
  const Logic4Word& word = kValue.words[bit / 64];
  const uint64_t kMask = uint64_t{1} << (bit % 64);
  return OneBitLiteral(arena, static_cast<size_t>((word.aval & kMask) != 0),
                       static_cast<size_t>((word.bval & kMask) != 0));
}

// §11.4.10: whether `t` is an operator that works a bit at a time, the ~ of
// one operand or the &, | or ^ of two, whose bit k is made of the operands'
// bits k alone.
bool IsBitwise(const Expr* t) {
  if (t->kind == ExprKind::kUnary) return t->op == TokenKind::kTilde;
  return t->kind == ExprKind::kBinary &&
         (t->op == TokenKind::kAmp || t->op == TokenKind::kPipe ||
          t->op == TokenKind::kCaret);
}

// Whether every operand under the bitwise operators of `t` measures a width
// (GateTerminalWidth), so that each of its bits can be addressed. Any other
// operation among them measures none, and its bits are not its operands'.
bool OperandsMeasured(const Expr* t, const RtlirModule* mod,
                      const ScopeMap& scope) {
  if (!IsBitwise(t)) return GateTerminalWidth(t, mod, scope) != 0;
  return OperandsMeasured(t->lhs, mod, scope) &&
         (t->rhs == nullptr || OperandsMeasured(t->rhs, mod, scope));
}

// §11.8.1: whether the bitwise terminal `t` is signed, which it is where every
// operand under its operators is: a signal declared signed or a literal
// written signed. A select, a concatenation and anything else is unsigned.
bool TerminalSigned(const Expr* t, const RtlirModule* mod) {
  if (IsBitwise(t)) {
    return TerminalSigned(t->lhs, mod) &&
           (t->rhs == nullptr || TerminalSigned(t->rhs, mod));
  }
  if (t->kind == ExprKind::kIntegerLiteral) return IsSignedLiteral(t->text);
  return t->kind == ExprKind::kIdentifier &&
         FindSignalDecl(t->text, mod).is_signed;
}

// The bit `bit` of `t`, an operand under the bitwise operators of a terminal,
// each operand extended to the terminal's width before the operators apply
// (§11.6.1): past an operand's own width its bit is the operand's sign bit
// where `extend_sign`, the terminal being signed (§11.8.2), and 0 where not.
// An operand of one bit is its own bit.
Expr* OperandBitAt(Expr* t, uint32_t bit, bool extend_sign,
                   const GateArraySite& site) {
  if (IsBitwise(t)) {
    auto* e = site.arena.Create<Expr>();
    e->kind = t->kind;
    e->range = t->range;
    e->op = t->op;
    e->lhs = OperandBitAt(t->lhs, bit, extend_sign, site);
    if (t->rhs != nullptr) {
      e->rhs = OperandBitAt(t->rhs, bit, extend_sign, site);
    }
    return e;
  }
  const uint32_t kWidth = GateTerminalWidth(t, site.mod, site.scope);
  if (bit >= kWidth) {
    if (!extend_sign) return OneBitLiteral(site.arena, 0, 0);
    bit = kWidth - 1;
  }
  return kWidth == 1
             ? t
             : GateTerminalBit(t, bit, site.mod, site.scope, site.arena);
}

// How far above the least significant end of the range `range` the low end of
// the select `sel` stands: its least significant bit, whichever bound or
// indexed form writes it.
int64_t SelectLowOffset(const Expr* sel, const PackedRange& range,
                        const ScopeMap& scope) {
  int64_t first = ConstEvalInt(sel->index, scope).value_or(0);
  int64_t second = ConstEvalInt(sel->index_end, scope).value_or(0);
  if (sel->is_part_select_plus) second = first + second - 1;
  if (sel->is_part_select_minus) second = first - second + 1;
  return std::min(range.OffsetOf(first), range.OffsetOf(second));
}

// How many indices `range` covers.
int64_t RangeWidth(const PackedRange& range) {
  return range.HighIndex() - range.LowIndex() + 1;
}

// §7.4.5 and §7.4.6: the packed dimensions, outermost first, of what the
// select `sel` names where it is written with one index of a signal and names
// more than a bit: every packed dimension of an unpacked array's element, or
// those inside the outermost one of a packed array, the subarray the index
// selects. None for a part-select, a select of a vector's bit, or a select of
// a name that is no variable, net or port of `mod`.
std::vector<PackedRange> SelectedDims(const Expr* sel, const RtlirModule* mod,
                                      const ScopeMap& scope) {
  if (sel->index_end != nullptr) return {};
  const FoundSignalDecl kDecl = FindSignalDecl(sel->base->text, mod);
  if (kDecl.dtype == nullptr) return {};
  auto fold = [&](const Expr* left, const Expr* right) {
    return PackedRange{ConstEvalInt(left, scope).value_or(0),
                       ConstEvalInt(right, scope).value_or(0)};
  };
  std::vector<PackedRange> dims;
  if (kDecl.unpacked) {
    dims.push_back(
        fold(kDecl.dtype->packed_dim_left, kDecl.dtype->packed_dim_right));
  }
  for (const auto& [left, right] : kDecl.dtype->extra_packed_dims) {
    dims.push_back(fold(left, right));
  }
  return dims;
}

// The bit `bit` above the least significant end of the select `sel`, whose
// packed dimensions are `dims`, outermost first: a select of it per
// dimension, the innermost dimension's index running fastest (§7.4.5).
Expr* SelectedBitAt(Arena& arena, Expr* sel, int64_t bit,
                    const std::vector<PackedRange>& dims) {
  std::vector<int64_t> indices(dims.size());
  for (size_t i = dims.size(); i > 0; --i) {
    const PackedRange& dim = dims[i - 1];
    indices[i - 1] = dim.IndexAtOffset(bit % RangeWidth(dim));
    bit /= RangeWidth(dim);
  }
  Expr* e = sel;
  for (int64_t index : indices) e = MakeBitSelectAt(arena, e, index);
  return e;
}

}  // namespace

uint32_t GateTerminalWidth(const Expr* t, const RtlirModule* mod,
                           const ScopeMap& scope) {
  // A select of a subarray or an unpacked element is as wide as its
  // dimensions. SelectLhsWidth gives any select written with one index one
  // bit, so `p[1]` of `wire [1:0][1:0] p` was connected whole.
  if (t->kind == ExprKind::kSelect) {
    const std::vector<PackedRange> kDims = SelectedDims(t, mod, scope);
    if (kDims.empty()) return SelectLhsWidth(t, scope);
    int64_t width = 1;
    for (const PackedRange& dim : kDims) width *= RangeWidth(dim);
    return static_cast<uint32_t>(width);
  }
  // §5.7.1: a sized literal is as wide as its size says, and an unsized one
  // at least 32 bits. Asked of the declared signals, a literal measured 0 and
  // was connected whole, every instance reading its least significant bit.
  if (t->kind == ExprKind::kIntegerLiteral) {
    return LiteralWidth(t->text, t->int_val);
  }
  // §11.6.1: ~ is as wide as its operand, and &, | and ^ as the wider of
  // theirs; any other operator connects whole.
  if (IsBitwise(t)) {
    const uint32_t kLhs = GateTerminalWidth(t->lhs, mod, scope);
    return t->rhs == nullptr
               ? kLhs
               : std::max(kLhs, GateTerminalWidth(t->rhs, mod, scope));
  }
  if (t->kind != ExprKind::kConcatenation) return LookupLhsWidth(t, mod);
  uint32_t total = 0;
  for (const Expr* el : t->elements) {
    uint32_t w = GateTerminalWidth(el, mod, scope);
    if (w == 0) return 0;
    total += w;
  }
  return total;
}

// A named signal's bit, and a select's of one, are named by their index in the
// signal's declared range, so the bit an output terminal is written through
// stays a net lvalue; a concatenation's bit is its operand's that holds it.
// Called with a terminal GateTerminalWidth measures as wide as the array.
Expr* GateTerminalBit(Expr* t, uint32_t bit, const RtlirModule* mod,
                      const ScopeMap& scope, Arena& arena) {
  if (t->kind == ExprKind::kIdentifier) {
    PackedRange range = SignalDeclaredRange(t->text, mod, scope);
    return MakeBitSelectAt(arena, t, range.IndexAtOffset(bit));
  }
  if (t->kind == ExprKind::kSelect) {
    const std::vector<PackedRange> kDims = SelectedDims(t, mod, scope);
    if (!kDims.empty()) return SelectedBitAt(arena, t, bit, kDims);
    PackedRange range = SignalDeclaredRange(t->base->text, mod, scope);
    int64_t offset = SelectLowOffset(t, range, scope) + bit;
    return MakeBitSelectAt(arena, t->base, range.IndexAtOffset(offset));
  }
  if (t->kind == ExprKind::kIntegerLiteral) return LiteralBitAt(arena, t, bit);
  // §11.4.10: a bitwise operator's bit is the operator over its operands'
  // bits, so each instance connects to an expression of its own one bit, the
  // operands' bits the VPI model reports it over. Selected whole, the
  // operation had no object for its bit.
  if (IsBitwise(t) && OperandsMeasured(t, mod, scope)) {
    return OperandBitAt(t, bit, TerminalSigned(t, mod), {mod, scope, arena});
  }
  // Any other operator expression, an input terminal alone, is addressed as
  // [width-1:0].
  if (t->kind != ExprKind::kConcatenation) {
    return MakeBitSelectAt(arena, t, bit);
  }
  // A concatenation, which GateTerminalWidth measures as wide as the array,
  // holds the bit in one of its operands, counted from its last.
  auto it = t->elements.rbegin();
  while (bit >= GateTerminalWidth(*it, mod, scope)) {
    bit -= GateTerminalWidth(*it, mod, scope);
    ++it;
  }
  return GateTerminalBit(*it, bit, mod, scope, arena);
}

std::vector<Expr*> InstanceArrayElementTerminals(
    const std::vector<Expr*>& terms, const GateArraySite& site,
    uint32_t array_len, uint32_t p) {
  std::vector<Expr*> bit_terms;
  bit_terms.reserve(terms.size());
  for (auto* t : terms) {
    // §28.3.6: a terminal as wide as one instance's, one bit, connects to it
    // whole, so an array of one element, whose length is that width too,
    // takes its terminals as written.
    const bool kShared =
        array_len > 1 &&
        GateTerminalWidth(t, site.mod, site.scope) == array_len;
    bit_terms.push_back(
        kShared ? GateTerminalBit(t, p, site.mod, site.scope, site.arena) : t);
  }
  return bit_terms;
}

}  // namespace delta
