#pragma once

#include <cstdint>
#include <utility>
#include <vector>

namespace delta {

enum class SequenceMethod : uint8_t {
  kTriggered,
  kMatched,
};

enum class SequenceMethodOperandKind : uint8_t {
  kNamedSequenceInstance,
  kUntypedFormalArgument,
  kSequenceTypedFormalArgument,
  kOther,
};
bool IsSequenceMethodOperandLegal(SequenceMethodOperandKind kind);

bool SequenceMethodResultIsSingleBit();

bool SequenceMethodResultDependsOnStartPoint();

enum class SequenceMethodContext : uint8_t {
  kAssertionStatement,
  kWaitStatement,
  kBooleanExpressionOutsideSequence,
  kSequenceExpression,
};

bool SequenceTreatsFormalAsLocalVar(bool formal_is_match_item_lvalue);

bool IsSequenceMethodContextLegal(SequenceMethod method,
                                  SequenceMethodContext context,
                                  bool sequence_treats_formal_as_local_var);

bool SequenceMethodStatusSetInObservedRegion();

enum class SequenceMethodPersistence : uint8_t {
  kThroughTimeStep,
  kUntilFirstDestinationClockTick,
};
SequenceMethodPersistence SequenceMethodStatusPersistence(
    SequenceMethod method);

bool SequenceMethodSampledValueIsCurrentValue();

bool EmptyMatchActivatesSequenceMethod();

bool TriggeredSequenceDependenciesAreAcyclic(
    int sequence_count,
    const std::vector<std::pair<int, int>>& triggered_edges);

enum class SequenceMethodClockContext : uint8_t {
  kExplicitlyClocked,
  kCheckerInstantiation,
  kModulePortConnection,
  kInterfaceOrProgramPortConnection,
  kFunctionOrTaskArgument,
  kEventExpressionInstance,
  kInferredFromSurroundingContext,
};

bool SequenceMethodClockIsInferredFromContext(SequenceMethodClockContext ctx);

bool InferredClockDefaultUsesSampledValueRules(bool actual_argument_provided);

}  // namespace delta
