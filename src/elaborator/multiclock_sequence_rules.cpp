#include "elaborator/multiclock_sequence_rules.h"

#include <cstddef>
#include <optional>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/multiclock_sequence.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/sequence_degeneracy.h"
#include "elaborator/sequence_match_class.h"
#include "parser/ast.h"

namespace delta {

namespace {

// The spelling of a clock, its events' edges and signals, the leading
// clock's for an operand under no clock of its own.
std::string ClockName(const std::vector<EventExpr>& clock,
                      const std::vector<EventExpr>& leading) {
  const std::vector<EventExpr>& named = clock.empty() ? leading : clock;
  std::string name;
  for (const EventExpr& ev : named) {
    if (!name.empty()) name += ", ";
    if (ev.edge == Edge::kPosedge) name += "posedge ";
    if (ev.edge == Edge::kNegedge) name += "negedge ";
    if (ev.signal != nullptr) name += ev.signal->text;
  }
  return name;
}

// What the rules are applied under: the leading clock, where to report, the
// declarations and the diagnostics.
struct MulticlockCheck {
  const std::vector<EventExpr>& leading;
  SourceLoc loc;
  const PropertyRegistry& registry;
  DiagEngine& diag;
};

const std::vector<EventExpr>& ClockAt(const SeqLinearBody& body, size_t i) {
  static const std::vector<EventExpr> kNone;
  return i < body.clocks.size() ? body.clocks[i] : kNone;
}

// §16.13.1: the operator joining the operand at `i` to the one before it:
// ##1, ##0 or any other delay.
MulticlockJoin JoinAt(const SeqLinearBody& body, size_t i) {
  const SeqCycleDelay& delay = body.delays[i];
  if (delay.min != delay.max) return MulticlockJoin::kOther;
  if (delay.max == 1) return MulticlockJoin::kSingleDelay;
  if (delay.max == 0) return MulticlockJoin::kZeroDelay;
  return MulticlockJoin::kOther;
}

// §16.13.1: whether the maximal singly clocked subsequence of the operands
// from `first` to `last` admits an empty match, read off the chain cut from
// the body with no delay before its first operand.
bool SegmentAdmitsEmpty(const SeqLinearBody& body, size_t first, size_t last,
                        const PropertyRegistry& registry) {
  SeqLinearBody segment;
  segment.locals = body.locals;
  SeqCycleDelay none;
  none.min = 0;
  none.max = 0;
  for (size_t i = first; i <= last; ++i) {
    segment.operands.push_back(body.operands[i]);
    segment.delays.push_back(i == first ? none : body.delays[i]);
    segment.match_items.push_back(body.match_items[i]);
    segment.repetitions.push_back(body.repetitions[i]);
  }
  return AdmitsAnyEmptyMatch(ClassifyBodyMatches(segment, registry));
}

// §16.13.1: the maximal singly clocked subsequences of one chain, each with
// the clock over it, the operator joining it to the one before and whether
// it admits an empty match.
std::vector<MulticlockSubsequence> SubsequencesOf(
    const SeqLinearBody& body, const std::vector<EventExpr>& leading,
    const PropertyRegistry& registry) {
  std::vector<MulticlockSubsequence> out;
  if (body.clocks.empty() || body.operands.empty()) return out;
  size_t first = 0;
  for (size_t i = 1; i <= body.operands.size(); ++i) {
    bool ends = i == body.operands.size() ||
                ClockName(ClockAt(body, i), leading) !=
                    ClockName(ClockAt(body, first), leading);
    if (!ends) continue;
    MulticlockSubsequence sub;
    sub.clock = ClockName(ClockAt(body, first), leading);
    sub.join = first == 0 ? MulticlockJoin::kLeading : JoinAt(body, first);
    sub.admits_empty = SegmentAdmitsEmpty(body, first, i - 1, registry);
    out.push_back(sub);
    first = i;
  }
  return out;
}

// Whether any operand of the chain is on a clock other than the leading.
bool NamesAnotherClock(const SeqLinearBody& body,
                       const std::vector<EventExpr>& leading) {
  for (const auto& clock : body.clocks) {
    if (!clock.empty() && ClockName(clock, leading) != ClockName({}, leading)) {
      return true;
    }
  }
  return false;
}

void ValidateBody(const SeqLinearBody& body, const MulticlockCheck& check);

// §16.13.1: differently clocked operands are combined by ##1 and ##0 alone,
// so an operand of `op` on a clock of its own is reported, and each
// operand's chain is checked on its own.
void ValidateOperands(const std::vector<SeqLinearBody>& operands,
                      const char* op, const MulticlockCheck& check) {
  for (const SeqLinearBody& operand : operands) {
    if (NamesAnotherClock(operand, check.leading)) {
      check.diag.Error(
          check.loc,
          std::string("differently clocked sequence operands may be joined "
                      "only by the single-delay (##1) or zero-delay (##0) "
                      "operator, not by ") +
              op,
          Subclause("16.13.1"));
    }
    ValidateBody(operand, check);
  }
}

void ValidateBody(const SeqLinearBody& body, const MulticlockCheck& check) {
  std::optional<std::string> breach = CheckMulticlockSequenceLegality(
      SubsequencesOf(body, check.leading, check.registry));
  if (breach.has_value()) {
    check.diag.Error(check.loc, *breach, Subclause("16.13.1"));
  }
  ValidateOperands(body.intersects, "intersect", check);
  ValidateOperands(body.conjuncts, "and", check);
  ValidateOperands(body.alternatives, "or", check);
}

}  // namespace

void ValidateMulticlockSequence(const ModuleItem* seq,
                                const std::vector<EventExpr>& leading,
                                SourceLoc loc, const PropertyRegistry& registry,
                                DiagEngine& diag) {
  if (seq == nullptr) return;
  ValidateBody(seq->seq_linear, MulticlockCheck{leading, loc, registry, diag});
}

void ValidateMulticlockSequences(const PropertyExprNode* node,
                                 const std::vector<EventExpr>& leading,
                                 SourceLoc loc,
                                 const PropertyRegistry& registry,
                                 DiagEngine& diag) {
  if (node == nullptr) return;
  ValidateMulticlockSequence(node->sequence, leading, loc, registry, diag);
  for (const PropertyExprNode* operand : node->operands) {
    ValidateMulticlockSequences(operand, leading, loc, registry, diag);
  }
}

}  // namespace delta
