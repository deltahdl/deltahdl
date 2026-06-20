#pragma once

#include <cstdint>

#include "elaborator/sequence_degeneracy.h"

namespace delta {

// §16.11 BNF: sequence_match_item is one of operator_assignment,
// inc_or_dec_expression, or subroutine_call. We carry the discriminator so
// the elaborator can apply per-kind rules without re-parsing.
enum class SequenceMatchItemKind : uint8_t {
  kOperatorAssignment,
  kIncOrDecExpression,
  kSubroutineCall,
};

// §16.11 lists the callable forms that may stand as a subroutine_call: task,
// task method, void function, void function method, and system task.
enum class AttachableSubroutineKind : uint8_t {
  kTask,
  kTaskMethod,
  kVoidFunction,
  kVoidFunctionMethod,
  kSystemTask,
};

bool IsAttachableSubroutineKind(AttachableSubroutineKind k);

// §16.11: it is an error to attach a subroutine_call or any
// sequence_match_item to a sequence that admits an empty match. This rule
// applies to all three sequence_match_item kinds, not just subroutine_call.
// We delegate to §16.12.22's classifier so the same "empty match" notion is
// shared by both subclauses.
bool IsSequenceMatchItemAttachLegal(SequenceMatchClass seq_class);

// §16.11: each argument of an attached subroutine call shall either be passed
// by value (as an input) or by reference (ref / const ref).
enum class SubroutineArgPassing : uint8_t {
  kByValueInput,
  kByRef,
  kByConstRef,
};

bool IsArgPassingAllowedForAttachedCall(SubroutineArgPassing kind);

// §16.11: an automatic variable may be passed as a constant input from a
// subroutine call in an assertion in procedural code (§16.14.6.1). It shall
// not be passed by reference, nor as a non-constant input, in any case.
bool IsAutomaticArgUseAllowed(SubroutineArgPassing kind,
                              bool from_procedural_assertion, bool is_constant);

// §16.11: a local variable may be passed into an attached call. If a local
// variable appears in an actual argument expression, that argument shall be
// passed by value.
bool IsLocalVarArgPassingLegal(bool local_var_in_arg_expr,
                               SubroutineArgPassing kind);

// §16.11: attached subroutine calls are executed at every end point of the
// sequence; for each end point, they execute in the order they appear in
// the list. They are scheduled in the Reactive region (like an action
// block). Assertion evaluation does not wait on, or receive data back from,
// any attached subroutine. We expose these as queryable scheduling facts.
enum class AttachedSubroutineSchedulingRegion : uint8_t {
  kReactive,
};

AttachedSubroutineSchedulingRegion AttachedSubroutineRegion();

bool AssertionEvalWaitsForAttachedSubroutine();

bool AttachedSubroutineRunsAtEveryEndPoint();

bool AttachedSubroutineCallsExecuteInListOrder();

// §16.11: a variable passed by value as an input shall be of a type allowed
// in §16.6. The caller resolves §16.6's type list elsewhere and surfaces a
// boolean indicating whether the variable's type is allowed there; this
// helper enforces §16.11's gating predicate on top of that result.
bool IsByValueInputArgumentTypeAllowed(bool type_allowed_in_16_6);

// §16.11: actual argument expressions that are passed by value use sampled
// values of the underlying variables, and the sampled values used are
// consistent with the variable values used to evaluate the sequence match.
// These two predicates surface the rule as queryable facts so the simulator
// can route a by-value attached-argument capture to the sampling path.
bool ByValueArgumentUsesSampledValuesOfUnderlying();
bool ByValueArgumentValueIsConsistentWithSequenceMatch();

}  // namespace delta
