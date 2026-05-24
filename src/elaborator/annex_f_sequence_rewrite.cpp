#include "elaborator/annex_f_sequence_rewrite.h"

#include <memory>

#include "elaborator/annex_f_grammar.h"

namespace delta {

std::shared_ptr<const SequenceExpr> RewriteSequenceUnderClock(
    const SequenceExpr& sequence, std::shared_ptr<const BooleanExpr> clock) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean: {
      // §F.5.1.1: T^s(b, c) = (!c[*0:$] ##1 c & b). The clock may tick any
      // number of times before the cycle in which both the clock and b hold.
      auto wait = SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(clock)));
      auto fire = SeqBoolean(BoolAnd(clock, sequence.boolean));
      return SeqConcat(wait, fire);
    }
    case SequenceExpr::Kind::kLocalVarSampling: {
      // §F.5.1.1: T^s((1, v = e), c) = (T^s(1, c) ##0 (1, v = e)). The
      // assignment is fused onto the clocked tick that 1 rewrites to.
      auto clocked_one = RewriteSequenceUnderClock(*SeqBoolean(BoolTrue()),
                                                   clock);
      return SeqFusion(clocked_one,
                       SeqLocalVarSampling(sequence.local_var_name));
    }
    case SequenceExpr::Kind::kClock:
      // §F.5.1.1: T^s((@(c2) r), c1) = T^s(r, c2). The inner clock c2
      // supersedes the incoming clock c1.
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
      // Parentheses only group; the clock passes through to the inner
      // sequence unchanged.
      return SeqParen(RewriteSequenceUnderClock(*sequence.lhs, clock));
    case SequenceExpr::Kind::kLocalVarDecl:
      return SeqLocalVarDecl(
          sequence.local_var_type, sequence.local_var_name,
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
      // Already unclocked: nothing to rewrite.
      return std::make_shared<SequenceExpr>(sequence);
  }
}

}  // namespace delta
