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
      return {};
    case SequenceExpr::Kind::kLocalVarDecl:
      return Difference(SampleLocals(*sequence.lhs), {sequence.local_var_name});
    case SequenceExpr::Kind::kLocalVarSampling:
      return {sequence.local_var_name};
    case SequenceExpr::Kind::kParen:
      return SampleLocals(*sequence.lhs);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
      return Union(SampleLocals(*sequence.lhs), SampleLocals(*sequence.rhs));
    case SequenceExpr::Kind::kFirstMatch:
      return SampleLocals(*sequence.lhs);
    case SequenceExpr::Kind::kNullRepeat:
      return {};
    case SequenceExpr::Kind::kUnboundedRepeat:
      return SampleLocals(*sequence.lhs);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      return {};
  }
  return {};
}

std::set<std::string> BlockLocals(const SequenceExpr& sequence) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean:
      return {};
    case SequenceExpr::Kind::kLocalVarDecl:
      return Difference(BlockLocals(*sequence.lhs), {sequence.local_var_name});
    case SequenceExpr::Kind::kLocalVarSampling:
      return {};
    case SequenceExpr::Kind::kParen:
      return BlockLocals(*sequence.lhs);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
      return Union(
          Difference(BlockLocals(*sequence.lhs), FlowLocals({}, *sequence.rhs)),
          BlockLocals(*sequence.rhs));
    case SequenceExpr::Kind::kOr:
      return Union(BlockLocals(*sequence.lhs), BlockLocals(*sequence.rhs));
    case SequenceExpr::Kind::kIntersect:
      return Union(
          Union(BlockLocals(*sequence.lhs), BlockLocals(*sequence.rhs)),
          Intersect(SampleLocals(*sequence.lhs), SampleLocals(*sequence.rhs)));
    case SequenceExpr::Kind::kFirstMatch:
      return BlockLocals(*sequence.lhs);
    case SequenceExpr::Kind::kNullRepeat:
      return {};
    case SequenceExpr::Kind::kUnboundedRepeat:
      return BlockLocals(*sequence.lhs);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      return {};
  }
  return {};
}

std::set<std::string> FlowLocals(const std::set<std::string>& incoming,
                                 const SequenceExpr& sequence) {
  switch (sequence.kind) {
    case SequenceExpr::Kind::kBoolean:
      return incoming;
    case SequenceExpr::Kind::kLocalVarDecl: {
      const std::set<std::string> kHidden{sequence.local_var_name};
      std::set<std::string> kept = Intersect(incoming, kHidden);
      std::set<std::string> inner = Difference(
          FlowLocals(Difference(incoming, kHidden), *sequence.lhs), kHidden);
      return Union(kept, inner);
    }
    case SequenceExpr::Kind::kLocalVarSampling:
      return Union(incoming, {sequence.local_var_name});
    case SequenceExpr::Kind::kParen:
      return FlowLocals(incoming, *sequence.lhs);
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
      return FlowLocals(FlowLocals(incoming, *sequence.lhs), *sequence.rhs);
    case SequenceExpr::Kind::kOr:
      return Intersect(FlowLocals(incoming, *sequence.lhs),
                       FlowLocals(incoming, *sequence.rhs));
    case SequenceExpr::Kind::kIntersect:
      return Difference(Union(FlowLocals(incoming, *sequence.lhs),
                              FlowLocals(incoming, *sequence.rhs)),
                        BlockLocals(sequence));
    case SequenceExpr::Kind::kFirstMatch:
      return FlowLocals(incoming, *sequence.lhs);
    case SequenceExpr::Kind::kNullRepeat:
      return incoming;
    case SequenceExpr::Kind::kUnboundedRepeat:
      return FlowLocals(incoming, *sequence.lhs);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      return incoming;
  }
  return incoming;
}

}  // namespace delta
