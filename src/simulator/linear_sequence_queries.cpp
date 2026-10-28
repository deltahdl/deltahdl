// The queries the sequence monitor and the lowering make of a flattened
// sequence, kept apart from the flattening itself.

#include <cstddef>
#include <functional>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/sequence_flatten.h"

namespace delta {

void ForEachLinearSequenceExpr(const LinearSequence& body,
                               const std::function<void(const Expr*)>& fn) {
  for (const Expr* operand : body.operands) fn(operand);
  for (const auto& items : body.match_items) {
    for (const SeqMatchAssign& item : items) {
      if (item.rhs != nullptr) fn(item.rhs);
      if (item.call != nullptr) fn(item.call);
    }
  }
  for (const SeqThroughout& guard : body.throughouts) fn(guard.cond);
  for (const LinearSequence& inner : body.intersects) {
    ForEachLinearSequenceExpr(inner, fn);
  }
  for (const LinearSequence& inner : body.conjuncts) {
    ForEachLinearSequenceExpr(inner, fn);
  }
  for (const LinearSequence& inner : body.alternatives) {
    ForEachLinearSequenceExpr(inner, fn);
  }
  for (const auto& entry : body.nested) {
    ForEachLinearSequenceExpr(*entry.second, fn);
  }
}

const std::vector<EventExpr>& OperandClock(const LinearSequence& body,
                                           size_t pos) {
  static const std::vector<EventExpr> kNone;
  return pos < body.operand_clocks.size() ? body.operand_clocks[pos] : kNone;
}

bool NamesAnotherClock(const LinearSequence& body) {
  for (const auto& clock : body.operand_clocks) {
    if (clock.empty()) continue;
    if (clock.size() != body.clock.size()) return true;
    for (size_t i = 0; i < clock.size(); ++i) {
      const EventExpr& a = clock[i];
      const EventExpr& b = body.clock[i];
      if (a.edge != b.edge || !SamePath(a.signal, b.signal)) return true;
    }
  }
  return false;
}

int OperandClockIndex(const LinearSequence& body, size_t pos) {
  return pos < body.operand_clock_index.size() ? body.operand_clock_index[pos]
                                               : 0;
}

}  // namespace delta
