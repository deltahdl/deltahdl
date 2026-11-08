#include "elaborator/annex_f_sequence_rewrite.h"

#include <memory>
#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"

namespace delta {

namespace {

void CollectLocalVariableNames(const SequenceExpr& sequence,
                               std::set<std::string>& names) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kLocalVarDecl:
      names.insert(sequence.local_var_name);
      CollectLocalVariableNames(*sequence.lhs, names);
      return;
    case SequenceExpr::Kind::kLocalVarSampling:
      names.insert(sequence.local_var_name);
      return;
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
      CollectLocalVariableNames(*sequence.lhs, names);
      CollectLocalVariableNames(*sequence.rhs, names);
      return;
    case SequenceExpr::Kind::kClock:
      CollectLocalVariableNames(*sequence.rhs, names);
      return;
    case SequenceExpr::Kind::kParen:
    case SequenceExpr::Kind::kFirstMatch:
    case SequenceExpr::Kind::kNullRepeat:
    case SequenceExpr::Kind::kUnboundedRepeat:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      CollectLocalVariableNames(*sequence.lhs, names);
      return;
    case SequenceExpr::Kind::kBoolean:
      return;
  }
}

void CollectBooleanAtoms(const BooleanExpr& boolean,
                         std::set<std::string>& atoms) {
  switch (boolean.kind) {
    case BooleanExpr::Kind::kAtom:
      atoms.insert(boolean.atom);
      return;
    case BooleanExpr::Kind::kNot:
      CollectBooleanAtoms(*boolean.operand_a, atoms);
      return;
    case BooleanExpr::Kind::kAnd:
      CollectBooleanAtoms(*boolean.operand_a, atoms);
      CollectBooleanAtoms(*boolean.operand_b, atoms);
      return;
    case BooleanExpr::Kind::kTrue:
      return;
  }
}

bool EventConditionReadsLocal(const BooleanExpr& event,
                              const std::set<std::string>& locals) {
  std::set<std::string> atoms;
  CollectBooleanAtoms(event, atoms);
  for (const std::string& atom : atoms) {
    if (locals.count(atom) != 0) {
      return true;
    }
  }
  return false;
}

bool AllClockEventsIndependent(const SequenceExpr& sequence,
                               const std::set<std::string>& locals) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kClock:
      if (EventConditionReadsLocal(*sequence.boolean, locals)) {
        return false;
      }
      return AllClockEventsIndependent(*sequence.rhs, locals);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
      return AllClockEventsIndependent(*sequence.lhs, locals) &&
             AllClockEventsIndependent(*sequence.rhs, locals);
    case SequenceExpr::Kind::kParen:
    case SequenceExpr::Kind::kFirstMatch:
    case SequenceExpr::Kind::kNullRepeat:
    case SequenceExpr::Kind::kUnboundedRepeat:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
    case SequenceExpr::Kind::kLocalVarDecl:
      return AllClockEventsIndependent(*sequence.lhs, locals);
    case SequenceExpr::Kind::kBoolean:
    case SequenceExpr::Kind::kLocalVarSampling:
      return true;
  }
  return true;
}

}  // namespace

std::shared_ptr<const SequenceExpr> RewriteSequenceUnderClock(
    const SequenceExpr& sequence,
    const std::shared_ptr<const BooleanExpr>& clock) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean: {
      auto wait = SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(clock)));
      auto fire = SeqBoolean(BoolAnd(clock, sequence.boolean));
      return SeqConcat(wait, fire);
    }
    case SequenceExpr::Kind::kLocalVarSampling: {
      auto clocked_one =
          RewriteSequenceUnderClock(*SeqBoolean(BoolTrue()), clock);
      return SeqFusion(clocked_one,
                       SeqLocalVarSampling(sequence.local_var_name));
    }
    case SequenceExpr::Kind::kClock:
      return RewriteSequenceUnderClock(*sequence.rhs, sequence.boolean);
    case SequenceExpr::Kind::kConcat:
      return SeqConcat(RewriteSequenceUnderClock(*sequence.lhs, clock),
                       RewriteSequenceUnderClock(*sequence.rhs, clock));
    case SequenceExpr::Kind::kFusion:
      return SeqFusion(RewriteSequenceUnderClock(*sequence.lhs, clock),
                       RewriteSequenceUnderClock(*sequence.rhs, clock));
    case SequenceExpr::Kind::kOr:
      return SeqOr(RewriteSequenceUnderClock(*sequence.lhs, clock),
                   RewriteSequenceUnderClock(*sequence.rhs, clock));
    case SequenceExpr::Kind::kIntersect:
      return SeqIntersect(RewriteSequenceUnderClock(*sequence.lhs, clock),
                          RewriteSequenceUnderClock(*sequence.rhs, clock));
    case SequenceExpr::Kind::kFirstMatch:
      return SeqFirstMatch(RewriteSequenceUnderClock(*sequence.lhs, clock));
    case SequenceExpr::Kind::kNullRepeat:
      return SeqNullRepeat(RewriteSequenceUnderClock(*sequence.lhs, clock));
    case SequenceExpr::Kind::kUnboundedRepeat:
      return SeqUnboundedRepeat(
          RewriteSequenceUnderClock(*sequence.lhs, clock));
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      return SeqZeroOrMoreRepeat(
          RewriteSequenceUnderClock(*sequence.lhs, clock));
    case SequenceExpr::Kind::kParen:
      return SeqParen(RewriteSequenceUnderClock(*sequence.lhs, clock));
    case SequenceExpr::Kind::kLocalVarDecl:
      return SeqLocalVarDecl(sequence.local_var_type, sequence.local_var_name,
                             RewriteSequenceUnderClock(*sequence.lhs, clock));
  }
  return std::make_shared<SequenceExpr>(sequence);
}

std::shared_ptr<const SequenceExpr> RewriteClockedSequence(
    const SequenceExpr& sequence) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kClock:
      return RewriteSequenceUnderClock(*sequence.rhs, sequence.boolean);
    case SequenceExpr::Kind::kParen:
      return SeqParen(RewriteClockedSequence(*sequence.lhs));
    case SequenceExpr::Kind::kConcat:
      return SeqConcat(RewriteClockedSequence(*sequence.lhs),
                       RewriteClockedSequence(*sequence.rhs));
    case SequenceExpr::Kind::kLocalVarDecl:
      return SeqLocalVarDecl(sequence.local_var_type, sequence.local_var_name,
                             RewriteClockedSequence(*sequence.lhs));
    default:
      return std::make_shared<SequenceExpr>(sequence);
  }
}

bool ClockEventsAreLocalVariableIndependent(const SequenceExpr& sequence) {
  std::set<std::string> locals;
  CollectLocalVariableNames(sequence, locals);
  return AllClockEventsIndependent(sequence, locals);
}

}  // namespace delta
