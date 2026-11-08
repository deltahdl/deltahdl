#pragma once

#include <cstdint>
#include <optional>

namespace delta {

enum class RewriteStage : std::uint8_t {
  kProperties,
  kSequences,
};

RewriteStage FirstRewriteStage();

RewriteStage NextRewriteStage(RewriteStage stage);

enum class SequenceInstanceContext : std::uint8_t {
  kClockingEventOperand,
  kSequenceMethodOperand,
  kOrdinary,
};

bool SequenceInstanceNeedsItemWrap(SequenceInstanceContext context);

enum class ActualArgumentSource : std::uint8_t {
  kBoundInInstance,
  kDeclaredDefault,
};

std::optional<ActualArgumentSource> ActualArgumentFor(bool bound_in_instance,
                                                      bool default_declared);

enum class FormalKind : std::uint8_t {
  kUntyped,
  kTypedNonMatching,
  kTypedMatching,
  kLocalVariable,
};

enum class ActualNature : std::uint8_t {
  kOther,
  kDollarOrLvalue,
  kCastingType,
  kSequenceMethodOperand,
};

enum class ReferenceReplacement : std::uint8_t {
  kActualDirect,
  kItemCastInferredType,
  kItemCastToFormalType,
  kItemCastTypeOfFormal,
  kItemActual,
  kParenthesizedActual,
};

ReferenceReplacement ReplaceFormalReference(FormalKind kind,
                                            ActualNature actual);

bool ReplacementMayStandAsMatchItemLvalue(ReferenceReplacement replacement);

bool ParenthesizedActualNeedsParentheses(bool reference_already_parenthesized);

enum class LocalVarDirection : std::uint8_t {
  kInput,
  kInout,
  kOutput,
};

struct LocalVarSubstitution {
  bool declaration_has_initializer = false;
  bool appends_match_assignment = false;
};

LocalVarSubstitution LocalVariableFlatten(LocalVarDirection direction);

LocalVarSubstitution PropertyLocalVariableFlatten();

enum class FlattenTarget : std::uint8_t {
  kProperty,
  kSequence,
};

struct FlattenedFormShape {
  bool local_var_declarations_ordered = false;
  bool appends_match_item_assignments = false;
  bool match_item_assignments_ordered = false;
  bool enclosed_in_parentheses = false;
};

FlattenedFormShape FlattenedForm(FlattenTarget target);

}  // namespace delta
