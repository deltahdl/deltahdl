#pragma once

#include <cstdint>

#include "elaborator/sequence_degeneracy.h"

namespace delta {

enum class SequenceMatchItemKind : uint8_t {
  kOperatorAssignment,
  kIncOrDecExpression,
  kSubroutineCall,
};

enum class AttachableSubroutineKind : uint8_t {
  kTask,
  kTaskMethod,
  kVoidFunction,
  kVoidFunctionMethod,
  kSystemTask,
};

bool IsAttachableSubroutineKind(AttachableSubroutineKind k);

bool IsSequenceMatchItemAttachLegal(SequenceMatchClass seq_class);

enum class SubroutineArgPassing : uint8_t {
  kByValueInput,
  kByRef,
  kByConstRef,
  kCopiedOut,
  kCopiedInOut,
};

bool IsArgPassingAllowedForAttachedCall(SubroutineArgPassing kind);

bool IsAutomaticArgUseAllowed(SubroutineArgPassing kind,
                              bool from_procedural_assertion, bool is_constant);

bool IsLocalVarArgPassingLegal(bool local_var_in_arg_expr,
                               SubroutineArgPassing kind);

enum class AttachedSubroutineSchedulingRegion : uint8_t {
  kReactive,
};

AttachedSubroutineSchedulingRegion AttachedSubroutineRegion();

bool AssertionEvalWaitsForAttachedSubroutine();

bool AttachedSubroutineRunsAtEveryEndPoint();

bool AttachedSubroutineCallsExecuteInListOrder();

bool IsByValueInputArgumentTypeAllowed(bool type_allowed_in_16_6);

bool ByValueArgumentUsesSampledValuesOfUnderlying();
bool ByValueArgumentValueIsConsistentWithSequenceMatch();

}  // namespace delta
