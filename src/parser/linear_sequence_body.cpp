#include "parser/linear_sequence_body.h"

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// §16.9.9: a throughout inside the group, among the first `guards`, spans
// the copy of the group `shift` operands on as it did the first.
void CopyGroupGuards(SeqLinearBody& body, size_t first, size_t guards,
                     size_t shift) {
  for (size_t g = 0; g < guards; ++g) {
    SeqThroughout guard = body.throughouts[g];
    if (guard.first < first) continue;
    guard.first += shift;
    guard.last += shift;
    body.throughouts.push_back(guard);
  }
}

}  // namespace

bool IsNoDelay(const SeqCycleDelay& delay) {
  return delay.min == 0 && delay.max == 0 && delay.min_expr == nullptr &&
         delay.max_expr == nullptr;
}

SeqCycleDelay AddSeqDelays(const SeqCycleDelay& a, const SeqCycleDelay& b) {
  if (IsNoDelay(a)) return b;
  SeqCycleDelay sum;
  sum.min = a.min + b.min;
  bool unbounded =
      a.max == SeqCycleDelay::kUnbounded || b.max == SeqCycleDelay::kUnbounded;
  sum.max = unbounded ? SeqCycleDelay::kUnbounded : a.max + b.max;
  return sum;
}

void PushOperandClock(SeqLinearBody& body,
                      const std::vector<EventExpr>& clock) {
  if (clock.empty() && body.clocks.empty()) return;
  while (body.clocks.size() + 1 < body.operands.size()) {
    body.clocks.emplace_back();
  }
  body.clocks.push_back(clock);
}

bool UnrollGroupRepetition(SeqLinearBody& body, size_t first,
                           const SeqRepetition& rep) {
  if (rep.kind == SeqRepetition::Kind::kNone) return true;
  if (rep.kind != SeqRepetition::Kind::kConsecutive) return false;
  size_t n = body.operands.size() - first;
  size_t guards = body.throughouts.size();
  for (uint32_t k = 1; k < rep.min; ++k) {
    for (size_t i = 0; i < n; ++i) {
      body.operands.push_back(body.operands[first + i]);
      SeqCycleDelay delay = body.delays[first + i];
      if (i == 0) delay = SeqCycleDelay{};
      body.delays.push_back(delay);
      body.match_items.push_back(body.match_items[first + i]);
      body.repetitions.push_back(body.repetitions[first + i]);
      if (!body.clocks.empty()) body.clocks.push_back(body.clocks[first + i]);
    }
    CopyGroupGuards(body, first, guards, n * k);
  }
  return true;
}

void MarkEmptyMatchItems(const SeqLinearBody& body, size_t first,
                         std::vector<SeqMatchAssign>& items) {
  if (body.operands.size() != first + 1) return;
  const SeqRepetition& rep = body.repetitions[first];
  if (rep.kind == SeqRepetition::Kind::kNone || rep.min_expr != nullptr ||
      rep.min != 0) {
    return;
  }
  for (SeqMatchAssign& item : items) item.on_empty_match = true;
}

void WrapWithinOperand(SeqLinearBody& body, Expr* lead, Expr* trail) {
  SeqRepetition any;
  any.kind = SeqRepetition::Kind::kConsecutive;
  any.min = 0;
  any.max = SeqCycleDelay::kUnbounded;
  SeqCycleDelay none;
  none.min = 0;
  none.max = 0;
  SeqCycleDelay one;
  one.min = 1;
  one.max = 1;
  SeqLinearBody wrapped;
  wrapped.operands.push_back(lead);
  wrapped.delays.push_back(none);
  wrapped.match_items.emplace_back();
  wrapped.repetitions.push_back(any);
  for (size_t i = 0; i < body.operands.size(); ++i) {
    wrapped.operands.push_back(body.operands[i]);
    wrapped.delays.push_back(i == 0 ? AddSeqDelays(one, body.delays[0])
                                    : body.delays[i]);
    wrapped.match_items.push_back(body.match_items[i]);
    wrapped.repetitions.push_back(body.repetitions[i]);
  }
  wrapped.operands.push_back(trail);
  wrapped.delays.push_back(one);
  wrapped.match_items.emplace_back();
  wrapped.repetitions.push_back(any);
  for (SeqThroughout guard : body.throughouts) {
    guard.first += 1;
    guard.last += 1;
    wrapped.throughouts.push_back(guard);
  }
  if (!body.clocks.empty()) {
    wrapped.clocks.emplace_back();
    wrapped.clocks.insert(wrapped.clocks.end(), body.clocks.begin(),
                          body.clocks.end());
    wrapped.clocks.emplace_back();
  }
  body.operands = std::move(wrapped.operands);
  body.delays = std::move(wrapped.delays);
  body.match_items = std::move(wrapped.match_items);
  body.repetitions = std::move(wrapped.repetitions);
  body.throughouts = std::move(wrapped.throughouts);
  body.clocks = std::move(wrapped.clocks);
}

}  // namespace delta
