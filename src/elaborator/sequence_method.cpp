#include "elaborator/sequence_method.h"

#include <cstddef>
#include <utility>
#include <vector>

namespace delta {

bool IsSequenceMethodOperandLegal(SequenceMethodOperandKind kind) {
  switch (kind) {
    case SequenceMethodOperandKind::kNamedSequenceInstance:
    case SequenceMethodOperandKind::kUntypedFormalArgument:
    case SequenceMethodOperandKind::kSequenceTypedFormalArgument:
      return true;
    case SequenceMethodOperandKind::kOther:
      return false;
  }
  return false;
}

bool SequenceMethodResultIsSingleBit() { return true; }

bool SequenceMethodResultDependsOnStartPoint() { return false; }

bool SequenceTreatsFormalAsLocalVar(bool formal_is_match_item_lvalue) {
  return formal_is_match_item_lvalue;
}

bool IsSequenceMethodContextLegal(SequenceMethod method,
                                  SequenceMethodContext context,
                                  bool sequence_treats_formal_as_local_var) {
  switch (method) {
    case SequenceMethod::kTriggered:
      switch (context) {
        case SequenceMethodContext::kSequenceExpression:
        case SequenceMethodContext::kAssertionStatement:
          return true;
        case SequenceMethodContext::kWaitStatement:
        case SequenceMethodContext::kBooleanExpressionOutsideSequence:
          return !sequence_treats_formal_as_local_var;
      }
      return false;
    case SequenceMethod::kMatched:
      return context == SequenceMethodContext::kSequenceExpression;
  }
  return false;
}

bool SequenceMethodStatusSetInObservedRegion() { return true; }

SequenceMethodPersistence SequenceMethodStatusPersistence(
    SequenceMethod method) {
  switch (method) {
    case SequenceMethod::kTriggered:
      return SequenceMethodPersistence::kThroughTimeStep;
    case SequenceMethod::kMatched:
      return SequenceMethodPersistence::kUntilFirstDestinationClockTick;
  }
  return SequenceMethodPersistence::kThroughTimeStep;
}

bool SequenceMethodSampledValueIsCurrentValue() { return true; }

bool EmptyMatchActivatesSequenceMethod() { return false; }

namespace {

bool HasCycleFrom(size_t node, const std::vector<std::vector<int>>& adjacency,
                  std::vector<int>& state) {
  state[node] = 1;
  for (int next : adjacency[node]) {
    const auto kNextIndex = static_cast<size_t>(next);
    if (state[kNextIndex] == 1) {
      return true;
    }
    if (state[kNextIndex] == 0 && HasCycleFrom(kNextIndex, adjacency, state)) {
      return true;
    }
  }
  state[node] = 2;
  return false;
}

}  // namespace

bool TriggeredSequenceDependenciesAreAcyclic(
    int sequence_count,
    const std::vector<std::pair<int, int>>& triggered_edges) {
  if (sequence_count <= 0) {
    return true;
  }
  std::vector<std::vector<int>> adjacency(static_cast<size_t>(sequence_count));
  for (const auto& edge : triggered_edges) {
    if (edge.first < 0 || edge.first >= sequence_count || edge.second < 0 ||
        edge.second >= sequence_count) {
      continue;
    }
    adjacency[static_cast<size_t>(edge.first)].push_back(edge.second);
  }
  std::vector<int> state(static_cast<size_t>(sequence_count), 0);
  for (size_t node = 0; node < static_cast<size_t>(sequence_count); ++node) {
    if (state[node] == 0 && HasCycleFrom(node, adjacency, state)) {
      return false;
    }
  }
  return true;
}

bool SequenceMethodClockIsInferredFromContext(SequenceMethodClockContext ctx) {
  return ctx != SequenceMethodClockContext::kExplicitlyClocked;
}

bool InferredClockDefaultUsesSampledValueRules(bool actual_argument_provided) {
  return !actual_argument_provided;
}

}  // namespace delta
