#include "elaborator/sequence_method.h"

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

bool SequenceMethodResultDependsOnStartPoint() {
  // §16.13.6: the result reflects only whether the end point has been reached,
  // never where the match began.
  return false;
}

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
          // Used within a sequence/property expression (a sequence context),
          // triggered is always available.
          return true;
        case SequenceMethodContext::kWaitStatement:
        case SequenceMethodContext::kBooleanExpressionOutsideSequence:
          // Outside a sequence context it is an error to apply triggered to a
          // sequence that treats its formal arguments as local variables.
          return !sequence_treats_formal_as_local_var;
      }
      return false;
    case SequenceMethod::kMatched:
      // matched can only be used in sequence expressions.
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

bool EmptyMatchActivatesSequenceMethod() {
  // §16.13.6 / §16.9.11: empty matches never activate triggered or matched.
  return false;
}

namespace {

// Depth-first cycle search over the triggered-dependency digraph.
bool HasCycleFrom(size_t node, const std::vector<std::vector<int>>& adjacency,
                  std::vector<int>& state) {
  // state: 0 = unvisited, 1 = on the current path, 2 = fully explored.
  state[node] = 1;
  for (int next : adjacency[node]) {
    const size_t next_index = static_cast<size_t>(next);
    if (state[next_index] == 1) {
      return true;
    }
    if (state[next_index] == 0 && HasCycleFrom(next_index, adjacency, state)) {
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
