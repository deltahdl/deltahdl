#pragma once

#include <cstdint>
#include <optional>

namespace delta {

// §F.4.1.1 spells out the rewriting algorithm that flattens a sequence or
// property containing named instances. It composes the `item` auxiliary of
// §F.4 (see rewrite_item.h) and the flattening bookkeeping of §F.4.1 (see
// property_rewrite.h); this file models the algorithm's own decisions:
//
//   * the order in which the two driving loops run (properties first, then
//     sequences),
//   * how a sequence instance is rewritten depending on where it occurs, and
//   * how a reference to a formal argument is replaced depending on the kind
//     of formal and the nature of the bound actual argument.
//
// The model is a set of pure decision functions: production code consults
// them while rewriting, and the §F.4.1.1 elaborator test observes the
// decisions. Name resolution and the construction of the flattened AST are
// out of scope here — §F.4.1 states the algorithm assumes names are already
// resolved.

// §F.4.1.1 main loop: the algorithm drains all property instances (each via
// flatten_property) before it touches any sequence instance (each via
// flatten_sequence). A property body may instantiate sequences, but a
// sequence never instantiates a property, so this fixed order guarantees the
// sequence pass sees a body whose property instances are already gone.
enum class RewriteStage : std::uint8_t {
  kProperties,  // first loop: while property instances remain
  kSequences,   // second loop: while sequence instances remain
};

// Returns the stage that the algorithm runs first.
RewriteStage FirstRewriteStage();

// Returns the stage that runs after `stage`, or the same stage if it is the
// last. Used to assert the two-loop ordering is exactly properties→sequences.
RewriteStage NextRewriteStage(RewriteStage stage);

// §F.4.1.1 main-loop step 2: where a sequence instance r occurs decides how
// its flattened form is spliced back in.
enum class SequenceInstanceContext : std::uint8_t {
  // (a) r appears in the event expression of a clocking_event.
  kClockingEventOperand,
  // (b) r is the operand of a sequence_method_call.
  kSequenceMethodOperand,
  // Anything else.
  kOrdinary,
};

// §F.4.1.1 main-loop step 2 vs step 3: in the clocking_event and
// sequence_method_call cases the flattened sequence is wrapped as
// item(sequence'flatten_sequence(r)); otherwise it is substituted as the
// bare flatten_sequence(r). Returns true iff the item(sequence'...) wrap is
// required.
bool SequenceInstanceNeedsItemWrap(SequenceInstanceContext context);

// §F.4.1.1 flatten_property/flatten_sequence step 2: the actual argument
// expression a_f that stands for a formal f of the copied declaration is the
// actual bound to f in the instance where one is, and the default actual
// declared for f where none is. A formal that is bound in the instance takes
// the bound actual whether or not a default is declared, since the default
// stands in only where no argument is bound. A formal neither bound nor
// defaulted has no a_f: §16.8 makes such an instance an error before the
// algorithm runs, so that case answers nullopt.
enum class ActualArgumentSource : std::uint8_t {
  kBoundInInstance,  // a_f is the actual bound to f in the instance
  kDeclaredDefault,  // a_f is the default actual declared for f
};

std::optional<ActualArgumentSource> ActualArgumentFor(bool bound_in_instance,
                                                      bool default_declared);

// §F.4.1.1 flatten_property/flatten_sequence steps 3–6 classify each formal
// argument of the instantiated declaration.
enum class FormalKind : std::uint8_t {
  // step 3: an untyped formal argument.
  kUntyped,
  // step 4: a typed formal, not a local variable, whose type does not match
  // (per 6.22.1) event, sequence, or property.
  kTypedNonMatching,
  // step 5: a typed formal whose type matches (per 6.22.1) event, sequence,
  // or property (and is therefore not a local variable).
  kTypedMatching,
  // step 6: a local variable formal argument.
  kLocalVariable,
};

// The aspects of an actual argument that the algorithm branches on while
// replacing a reference to its formal. Only the cases the text distinguishes
// are modeled.
enum class ActualNature : std::uint8_t {
  // No special form: an ordinary actual-argument expression.
  kOther,
  // step 3a: the actual is `$` or a variable_lvalue.
  kDollarOrLvalue,
  // step 4a: the formal's type t is a casting_type (see 6.24).
  kCastingType,
  // step 5a: the reference stands as the operand of a sequence_method_call.
  kSequenceMethodOperand,
};

// The shape of the substitution the algorithm performs for one reference to a
// formal argument (steps 3–5). Step 6 (local variables) is handled
// separately by LocalVariableFlatten because it prepends declarations rather
// than replacing references in place.
enum class ReferenceReplacement : std::uint8_t {
  // step 3a: replace the reference by the actual a_f, unchanged.
  kActualDirect,
  // step 3b: replace by item(type(a_f)'(a_f)) — cast through the actual's own
  // self-determined type.
  kItemCastInferredType,
  // step 4a: replace by item(t'(a_f)) — cast to the formal's casting_type t.
  kItemCastToFormalType,
  // step 4b: replace by item(type(t)'(a_f)) — cast through the formal type t.
  kItemCastTypeOfFormal,
  // step 5a: replace by item(a_f).
  kItemActual,
  // step 5b: replace by (a_f); the parentheses may be omitted when the
  // reference is itself already parenthesized.
  kParenthesizedActual,
};

// §F.4.1.1 flatten_property/flatten_sequence steps 3–5: given the kind of
// formal and the nature of the actual, return the replacement shape for a
// reference to that formal.
//
// The procedure is shared by flatten_property and flatten_sequence. Which
// types count as "matching" differs (only flatten_property can match the
// property type), but that difference is resolved when the caller classifies
// the formal into FormalKind, so the replacement shape depends only on the
// classification and the actual. Each FormalKind branch keys solely on the
// ActualNature distinction its own step draws and ignores the others.
ReferenceReplacement ReplaceFormalReference(FormalKind kind,
                                            ActualNature actual);

// §F.4.1.1 flatten_property/flatten_sequence step 4, by way of §16.8.1: a
// reference that step 4 replaces by a cast through the formal's type stands
// as an rvalue, so none of the references so replaced shall be the
// variable_lvalue in an operator_assignment or inc_or_dec_expression in a
// sequence_match_item. The replacements of the other steps carry no such
// note. Returns true iff a reference given the replacement may stand as
// that lvalue.
bool ReplacementMayStandAsMatchItemLvalue(ReferenceReplacement replacement);

// §F.4.1.1 flatten_property/flatten_sequence step 5b: the parentheses around
// the substituted actual a_f may be omitted where the reference is itself
// already enclosed in parentheses, and are required where it is not.
bool ParenthesizedActualNeedsParentheses(bool reference_already_parenthesized);

// §F.4.1.1 flatten_sequence step 6: a local variable formal argument is
// substituted by a prepended declaration, and, for the directions that pass a
// value back out, an assignment appended to the sequence's match items. (In
// flatten_property step 6 every local variable behaves like the input case:
// a declaration "t f = a_f;" with no match-item assignment.)
enum class LocalVarDirection : std::uint8_t {
  kInput,   // step 6a
  kInout,   // step 6b
  kOutput,  // step 6c
};

struct LocalVarSubstitution {
  // Whether the prepended declaration carries an initializer: "t f = a_f;"
  // for input/inout, "t f;" (no initializer) for output.
  bool declaration_has_initializer = false;
  // Whether an assignment "a_f = f" is appended to the body's match items so
  // the value flows back to the actual: true for inout and output.
  bool appends_match_assignment = false;
};

// Returns how a local variable formal of the given direction is flattened in
// flatten_sequence step 6.
LocalVarSubstitution LocalVariableFlatten(LocalVarDirection direction);

// §F.4.1.1 flatten_property step 6: every local variable formal argument of a
// property is flattened to the prepended declaration "t f = a_f;" and no
// match-item assignment, the shape flatten_sequence gives an input, since a
// property has no match items to carry a value back out through.
LocalVarSubstitution PropertyLocalVariableFlatten();

// §F.4.1.1 flatten_property and flatten_sequence, steps 6 and 7, and the
// note that closes the subclause: the shape of the expression each returns.
// Both prepend the local variable declarations of step 6 in any order and
// enclose the copied declarations and body in parentheses (step 7). Only
// flatten_sequence appends match-item assignments (steps 6b and 6c), and
// their order does not matter either, because by §16.8.2 distinct inout or
// output local variable formals are bound to distinct actuals, so no two
// assignments write the same a_f.
enum class FlattenTarget : std::uint8_t {
  kProperty,  // flatten_property
  kSequence,  // flatten_sequence
};

struct FlattenedFormShape {
  // Whether the prepended local variable declarations have a fixed order.
  bool local_var_declarations_ordered = false;
  // Whether match-item assignments a_f = f are appended to the body at all.
  bool appends_match_item_assignments = false;
  // Whether the appended match-item assignments have a fixed order.
  bool match_item_assignments_ordered = false;
  // Whether the returned expression is enclosed in parentheses.
  bool enclosed_in_parentheses = false;
};

FlattenedFormShape FlattenedForm(FlattenTarget target);

}  // namespace delta
