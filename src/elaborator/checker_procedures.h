#ifndef DELTA_ELABORATOR_CHECKER_PROCEDURES_H
#define DELTA_ELABORATOR_CHECKER_PROCEDURES_H

#include <cstdint>

namespace delta {

// §17.5 governs the procedures that may appear inside a checker body and the
// statements and sampling behavior of those procedures. The helpers here model
// only the rules the text of §17.5 states directly: which procedural blocks a
// checker admits, what an initial procedure may contain, which statements a
// checker always procedure may hold (and the always forms each is tied to), how
// expressions in those always procedures are sampled, and how a checker final
// procedure behaves. The clock inference the section illustrates is owned by
// §16.14.6 and the sampling mechanism by §16.5.1; this file only records how
// §17.5 scopes those rules onto checker procedures.

// §17.5: the kinds of procedural block that can be written in a checker body,
// including the always forms the section distinguishes.
enum class ProceduralBlockKind : uint8_t {
  kInitial,
  kFinal,
  kAlways,  // a general-purpose always procedure
  kAlwaysComb,
  kAlwaysLatch,
  kAlwaysFf,
};

// §17.5: the procedures allowed inside a checker body are the initial, always,
// and final procedures, and the only permitted always forms are always_comb,
// always_latch, and always_ff. A general-purpose always is therefore not
// allowed.
bool ProceduralBlockAllowedInChecker(ProceduralBlockKind kind);

// §17.5: the constructs an initial procedure in a checker body may hold. The
// procedure may contain let declarations and assertions, and a procedural
// timing control that uses an event control only.
enum class CheckerInitialContent : uint8_t {
  kLetDeclaration,
  kImmediateAssertion,
  kDeferredAssertion,
  kConcurrentAssertion,
  kEventTimingControl,  // a procedural timing control using an event control
  kDelayTimingControl,  // a delay-based timing control — not allowed
  kWaitTimingControl,   // a wait-based timing control — not allowed
};

// §17.5: an initial procedure in a checker may contain let declarations;
// immediate, deferred, and concurrent assertions; and a procedural timing
// control statement using an event control only. Delay- and wait-based timing
// controls are outside the permitted event-control-only form.
bool CheckerInitialProcedureAllows(CheckerInitialContent content);

// §17.5: the always forms a checker admits, used to qualify the per-statement
// rules below.
enum class CheckerAlwaysForm : uint8_t {
  kAlwaysComb,
  kAlwaysLatch,
  kAlwaysFf,
};

// §17.5: the statements a checker always procedure may contain.
enum class CheckerAlwaysStatement : uint8_t {
  kBlockingAssignment,
  kNonblockingAssignment,
  kSelectionStatement,
  kLoopStatement,
  kTimingEventControl,
  kSubroutineCall,
  kImmediateAssertion,
  kDeferredAssertion,
  kConcurrentAssertion,
  kLetDeclaration,
};

// §17.5: a checker always procedure may contain the listed statements. Two of
// them are tied to particular forms: blocking assignments are allowed in
// always_comb and always_latch procedures only, and timing event control is
// allowed in always_ff procedures only. The remaining statements are allowed in
// every checker always form.
bool CheckerAlwaysStatementAllowed(CheckerAlwaysStatement stmt,
                                   CheckerAlwaysForm form);

// §17.5: where an expression sits within a checker always procedure, used to
// decide whether it is implicitly sampled.
enum class CheckerAlwaysExpressionPosition : uint8_t {
  kEventControl,  // an expression appearing in the procedure's event control
  kBody,          // any other expression in the procedure
};

// §17.5: except for the variables used in the event control, all other
// expressions in an always_ff procedure are sampled (see §16.5.1), which also
// makes the expressions of immediate and deferred assertions there sampled.
// Expressions in always_comb and always_latch procedures are not implicitly
// sampled and use their current values.
bool CheckerAlwaysExpressionIsSampled(CheckerAlwaysForm form,
                                      CheckerAlwaysExpressionPosition position);

// §17.5: clock inference for checker procedures follows the rules in §16.14.6.
// The inference rules themselves are owned by §16.14.6; this records only that
// checker procedures fall within their scope.
bool CheckerProcedureClockInferenceFollowsSection16_14_6();

// §17.5: a final procedure may be specified within a checker in the same manner
// as in a module (see §9.2.3).
bool CheckerFinalProcedureIsAllowed();

// §17.5: a checker final procedure executes once at the end of simulation for
// every instantiation of the checker.
bool CheckerFinalProcedureRunsOncePerInstantiation();

// §17.5: there is no implied ordering in the execution of multiple final
// procedures.
bool CheckerFinalProceduresHaveImpliedOrdering();

// §17.5: the operation of a checker final procedure is independent of the
// instantiation context of the checker that contains it.
bool CheckerFinalProcedureDependsOnInstantiationContext();

// §17.5: a final procedure within a checker may include any construct allowed
// in a non-checker final procedure — neither more nor less. It therefore admits
// a construct exactly when a non-checker final procedure would.
bool CheckerFinalProcedureAllowsConstruct(bool allowed_in_non_checker_final);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CHECKER_PROCEDURES_H
