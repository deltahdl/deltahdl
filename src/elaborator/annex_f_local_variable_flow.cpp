#include "elaborator/annex_f_local_variable_flow.h"

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"

namespace delta {

namespace {

std::set<std::string> Union(const std::set<std::string>& a,
                            const std::set<std::string>& b) {
  std::set<std::string> result = a;
  result.insert(b.begin(), b.end());
  return result;
}

std::set<std::string> Intersect(const std::set<std::string>& a,
                                const std::set<std::string>& b) {
  std::set<std::string> result;
  for (const std::string& name : a) {
    if (b.count(name) != 0) {
      result.insert(name);
    }
  }
  return result;
}

std::set<std::string> Difference(const std::set<std::string>& a,
                                 const std::set<std::string>& b) {
  std::set<std::string> result;
  for (const std::string& name : a) {
    if (b.count(name) == 0) {
      result.insert(name);
    }
  }
  return result;
}

}  // namespace

std::set<std::string> SampleLocals(const SequenceExpr& sequence) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean:
      // §F.5.4: sample(b) = {}.
      return {};
    case SequenceExpr::Kind::kLocalVarDecl:
      // §F.5.4: sample((t v; R)) = sample(R) - {v}. The local declaration hides
      // v, so it is excluded from the names sampled by the inner sequence.
      return Difference(SampleLocals(*sequence.lhs), {sequence.local_var_name});
    case SequenceExpr::Kind::kLocalVarSampling:
      // §F.5.4: sample((1, v = e)) = {v}.
      return {sequence.local_var_name};
    case SequenceExpr::Kind::kParen:
      // §F.5.4: sample((R)) = sample(R).
      return SampleLocals(*sequence.lhs);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
      // §F.5.4: sample is the union of the operand samples for ##1, ##0, or,
      // and intersect alike.
      return Union(SampleLocals(*sequence.lhs), SampleLocals(*sequence.rhs));
    case SequenceExpr::Kind::kFirstMatch:
      // §F.5.4: sample(first_match(R)) = sample(R).
      return SampleLocals(*sequence.lhs);
    case SequenceExpr::Kind::kNullRepeat:
      // §F.5.4: sample(R[*0]) = {}.
      return {};
    case SequenceExpr::Kind::kUnboundedRepeat:
      // §F.5.4: sample(R[*1:$]) = sample(R).
      return SampleLocals(*sequence.lhs);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      // §F.5.4 is defined over unclocked sequences; the clock form and the
      // [*0:$] rewrite artifact are outside its grammar and sample nothing.
      return {};
  }
  return {};
}

std::set<std::string> BlockLocals(const SequenceExpr& sequence) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean:
      // §F.5.4: block(b) = {}.
      return {};
    case SequenceExpr::Kind::kLocalVarDecl:
      // §F.5.4: block((t v; R)) = block(R) - {v}.
      return Difference(BlockLocals(*sequence.lhs), {sequence.local_var_name});
    case SequenceExpr::Kind::kLocalVarSampling:
      // §F.5.4: block((1, v = e)) = {}.
      return {};
    case SequenceExpr::Kind::kParen:
      // §F.5.4: block((R)) = block(R).
      return BlockLocals(*sequence.lhs);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
      // §F.5.4: block((R1 ##1 R2)) and block((R1 ##0 R2)) are both
      // (block(R1) - flow({}, R2)) U block(R2). A name blocked by R1 stops
      // being blocked if it flows out of R2 on its own.
      return Union(
          Difference(BlockLocals(*sequence.lhs), FlowLocals({}, *sequence.rhs)),
          BlockLocals(*sequence.rhs));
    case SequenceExpr::Kind::kOr:
      // §F.5.4: block((R1 or R2)) = block(R1) U block(R2).
      return Union(BlockLocals(*sequence.lhs), BlockLocals(*sequence.rhs));
    case SequenceExpr::Kind::kIntersect:
      // §F.5.4: block((R1 intersect R2)) =
      // block(R1) U block(R2) U (sample(R1) ∩ sample(R2)). Names sampled in
      // both operands are blocked because the two threads would disagree.
      return Union(
          Union(BlockLocals(*sequence.lhs), BlockLocals(*sequence.rhs)),
          Intersect(SampleLocals(*sequence.lhs), SampleLocals(*sequence.rhs)));
    case SequenceExpr::Kind::kFirstMatch:
      // §F.5.4: block(first_match(R)) = block(R).
      return BlockLocals(*sequence.lhs);
    case SequenceExpr::Kind::kNullRepeat:
      // §F.5.4: block(R[*0]) = {}.
      return {};
    case SequenceExpr::Kind::kUnboundedRepeat:
      // §F.5.4: block(R[*1:$]) = block(R).
      return BlockLocals(*sequence.lhs);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      // §F.5.4 is defined over unclocked sequences; the clock form and the
      // [*0:$] rewrite artifact are outside its grammar and block nothing.
      return {};
  }
  return {};
}

std::set<std::string> FlowLocals(const std::set<std::string>& incoming,
                                 const SequenceExpr& sequence) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean:
      // §F.5.4: flow(X, b) = X.
      return incoming;
    case SequenceExpr::Kind::kLocalVarDecl: {
      // §F.5.4: flow(X, (t v; R)) = (X ∩ {v}) U (flow(X - {v}, R) - {v}). The
      // declaration shadows any incoming v; only the inner sequence may let a
      // fresh v flow, and even that is stripped at the declaration boundary.
      const std::set<std::string> hidden{sequence.local_var_name};
      std::set<std::string> kept = Intersect(incoming, hidden);
      std::set<std::string> inner = Difference(
          FlowLocals(Difference(incoming, hidden), *sequence.lhs), hidden);
      return Union(kept, inner);
    }
    case SequenceExpr::Kind::kLocalVarSampling:
      // §F.5.4: flow(X, (1, v = e)) = X U {v}.
      return Union(incoming, {sequence.local_var_name});
    case SequenceExpr::Kind::kParen:
      // §F.5.4: flow(X, (R)) = flow(X, R).
      return FlowLocals(incoming, *sequence.lhs);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
      // §F.5.4: flow(X, (R1 ##1 R2)) and flow(X, (R1 ##0 R2)) both thread the
      // names through R1 and then R2.
      return FlowLocals(FlowLocals(incoming, *sequence.lhs), *sequence.rhs);
    case SequenceExpr::Kind::kOr:
      // §F.5.4: flow(X, (R1 or R2)) = flow(X, R1) ∩ flow(X, R2). Only names
      // that flow out of both alternatives are guaranteed to flow out.
      return Intersect(FlowLocals(incoming, *sequence.lhs),
                       FlowLocals(incoming, *sequence.rhs));
    case SequenceExpr::Kind::kIntersect:
      // §F.5.4: flow(X, (R1 intersect R2)) =
      // (flow(X, R1) U flow(X, R2)) - block((R1 intersect R2)).
      return Difference(Union(FlowLocals(incoming, *sequence.lhs),
                              FlowLocals(incoming, *sequence.rhs)),
                        BlockLocals(sequence));
    case SequenceExpr::Kind::kFirstMatch:
      // §F.5.4: flow(X, first_match(R)) = flow(X, R).
      return FlowLocals(incoming, *sequence.lhs);
    case SequenceExpr::Kind::kNullRepeat:
      // §F.5.4: flow(X, R[*0]) = X.
      return incoming;
    case SequenceExpr::Kind::kUnboundedRepeat:
      // §F.5.4: flow(X, R[*1:$]) = flow(X, R).
      return FlowLocals(incoming, *sequence.lhs);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      // §F.5.4 is defined over unclocked sequences; the clock form and the
      // [*0:$] rewrite artifact are outside its grammar and pass names through.
      return incoming;
  }
  return incoming;
}

}  // namespace delta
