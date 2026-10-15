// §28.3.6: the terminals of an array of gate or switch instances, measured and
// shared out a bit per instance.

#include <algorithm>
#include <cstdint>

#include "common/arena.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

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

}  // namespace

uint32_t GateTerminalWidth(const Expr* t, const RtlirModule* mod,
                           const ScopeMap& scope) {
  if (t->kind == ExprKind::kSelect) return SelectLhsWidth(t, scope);
  // §11.6.1: ~ is as wide as its operand, and &, | and ^ as the wider of
  // theirs; any other operator connects whole.
  if (t->kind == ExprKind::kUnary && t->op == TokenKind::kTilde) {
    return GateTerminalWidth(t->lhs, mod, scope);
  }
  if (t->kind == ExprKind::kBinary &&
      (t->op == TokenKind::kAmp || t->op == TokenKind::kPipe ||
       t->op == TokenKind::kCaret)) {
    return std::max(GateTerminalWidth(t->lhs, mod, scope),
                    GateTerminalWidth(t->rhs, mod, scope));
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
    PackedRange range = SignalDeclaredRange(t->base->text, mod, scope);
    int64_t offset = SelectLowOffset(t, range, scope) + bit;
    return MakeBitSelectAt(arena, t->base, range.IndexAtOffset(offset));
  }
  // An operator expression, an input terminal alone, is addressed as
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

}  // namespace delta
