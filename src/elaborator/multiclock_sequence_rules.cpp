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
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

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

// §16.13.1: an operand of `op` on a clock other than the leading one.
void ReportOperandClock(const char* op, const MulticlockCheck& check) {
  check.diag.Error(
      check.loc,
      std::string("differently clocked sequence operands may be joined only "
                  "by the single-delay (##1) or zero-delay (##0) operator, "
                  "not by ") +
          op,
      Subclause("16.13.1"));
}

// §16.13.1: differently clocked operands are combined by ##1 and ##0 alone,
// so an operand of `op` on a clock of its own is reported, and each
// operand's chain is checked on its own.
void ValidateOperands(const std::vector<SeqLinearBody>& operands,
                      const char* op, const MulticlockCheck& check) {
  for (const SeqLinearBody& operand : operands) {
    if (NamesAnotherClock(operand, check.leading)) {
      ReportOperandClock(op, check);
    }
    ValidateBody(operand, check);
  }
}

// §16.9.1: the operator the chain of `body` is the first operand of, the
// one binding tightest among those written after it; nullptr where none is.
const char* FirstOperandOf(const SeqLinearBody& body) {
  if (body.within) return "within";
  if (!body.intersects.empty()) return "intersect";
  if (!body.conjuncts.empty()) return "and";
  if (!body.alternatives.empty()) return "or";
  return nullptr;
}

// Annex F.3.2 with F.2: whether a chain of `body` writes a clocking event
// other than the one named `in_force`, in an operand, in an operand of its
// intersects, conjuncts and alternatives or in a group read into a sequence
// of its own, a clock equal to the one in force being redundant.
bool WritesClockOtherThan(const SeqLinearBody& body,
                          const std::string& in_force) {
  for (const auto& clock : body.clocks) {
    if (!clock.empty() && ClockName(clock, clock) != in_force) return true;
  }
  for (const Expr* operand : body.operands) {
    const PropertyExprNode* tree = operand->property_actual;
    if (tree != nullptr && tree->kind == PropertyExprNode::Kind::kSequence &&
        tree->sequence != nullptr &&
        WritesClockOtherThan(tree->sequence->seq_linear, in_force)) {
      return true;
    }
  }
  auto any_writes = [&](const std::vector<SeqLinearBody>& operands) {
    for (const SeqLinearBody& operand : operands) {
      if (WritesClockOtherThan(operand, in_force)) return true;
    }
    return false;
  };
  return any_writes(body.intersects) || any_writes(body.conjuncts) ||
         any_writes(body.alternatives);
}

// The sequence a repeated operand stands for: a group read into a sequence
// of its own, or the named sequence an instance instantiates; nullptr for a
// Boolean operand.
const ModuleItem* RepeatedSequence(const Expr* operand,
                                   const PropertyRegistry& registry) {
  const PropertyExprNode* tree = operand->property_actual;
  if (tree != nullptr && tree->kind == PropertyExprNode::Kind::kSequence) {
    return tree->sequence;
  }
  const ModuleItem* decl = registry.FindInstance(operand);
  if (decl == nullptr || decl->kind != ModuleItemKind::kSequenceDecl) {
    return nullptr;
  }
  return decl;
}

// Annex F.3.2: a repetition has no clocked form, so the sequence a repeated
// operand stands for may write no clocking event but one F.2 eliminates as
// redundant, equal to the clock in force where the operand stands. Where no
// clock is known to be in force there, the leading clock being inherited
// from an instance not yet seen, the operand is left alone.
void ValidateRepeatedOperands(const SeqLinearBody& body,
                              const MulticlockCheck& check) {
  for (size_t i = 0; i < body.operands.size(); ++i) {
    if (body.repetitions[i].kind == SeqRepetition::Kind::kNone) continue;
    std::string in_force = ClockName(ClockAt(body, i), check.leading);
    if (in_force.empty()) continue;
    const ModuleItem* seq = RepeatedSequence(body.operands[i], check.registry);
    if (seq == nullptr) continue;
    bool other = (!seq->seq_clock.empty() &&
                  ClockName(seq->seq_clock, seq->seq_clock) != in_force) ||
                 WritesClockOtherThan(seq->seq_linear, in_force);
    if (!other) continue;
    check.diag.Error(check.loc,
                     "a repeated sequence may name no clocking event other "
                     "than the one in force where it is written",
                     Subclause("F.3.2"));
  }
}

void ValidateBody(const SeqLinearBody& body, const MulticlockCheck& check) {
  std::optional<std::string> breach = CheckMulticlockSequenceLegality(
      SubsequencesOf(body, check.leading, check.registry));
  if (breach.has_value()) {
    check.diag.Error(check.loc, *breach, Subclause("16.13.1"));
  }
  const char* op = FirstOperandOf(body);
  if (op != nullptr && NamesAnotherClock(body, check.leading)) {
    ReportOperandClock(op, check);
  }
  ValidateRepeatedOperands(body, check);
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
