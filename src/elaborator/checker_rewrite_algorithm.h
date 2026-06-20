#pragma once

#include "elaborator/rewrite_algorithm.h"

namespace delta {

// §F.4.2.1 specifies flatten_checker, the rewriting algorithm that flattens a
// checker containing instances of other checkers into a single checker without
// instances. Its per-reference substitution of an actual argument for a formal
// (steps 3–5) is identical to the sequence/property algorithm of §F.4.1.1, so
// this model reuses ReplaceFormalReference (see rewrite_algorithm.h) for those
// steps and adds only the decisions that are specific to the checker algorithm:
//
//   * its main loop drains a single kind of instance (checker instances),
//     unlike §F.4.1.1's two stages (properties, then sequences),
//   * it rewrites references to formal *input* arguments only, and a checker
//     input formal has no local-variable case — so flatten_checker has no
//     §F.4.1.1 step 6 and step 6 merely returns the body, and
//   * a reference replaced by a cast in step 4 shall not be a variable_lvalue
//     anywhere in the checker — a wider scope than §F.4.1.1's.
//
// The coarse-grained flattening machinery (legality, checker-instance counting,
// the input/output formal partition that step 2 relies on) lives in §F.4.2's
// checker_rewrite.h; this file is the algorithm's own decision model, which the
// §F.4.2.1 elaborator test observes. As §F.4.2 notes, name resolution and the
// construction of the flattened AST are out of scope.

// §F.4.2.1 main loop. The algorithm repeatedly selects an arbitrary checker
// instance and replaces it by flatten_checker, until no checker instances
// remain. There is exactly one kind of instance to drain.
enum class CheckerRewriteStage {
  kCheckerInstances,  // while there are checker instances in π
};

// The stage the main loop starts in.
CheckerRewriteStage FirstCheckerRewriteStage();

// The stage that follows `stage`. The checker loop has a single stage, so this
// is the identity — a fixed point that makes the "one loop, one instance kind"
// structure observable and distinguishes it from §F.4.1.1's two-stage loop.
CheckerRewriteStage NextCheckerRewriteStage(CheckerRewriteStage stage);

// §F.4.2.1 step 2 / step 6: the algorithm rewrites references for formal
// *input* arguments, each classified as untyped, typed-non-matching, or
// typed-matching. A checker formal input argument is never a local variable, so
// — unlike §F.4.1.1 — there is no kLocalVariable case and no step that prepends
// local variable declarations; step 6 only returns the body. Returns true iff
// `kind` is a formal kind that the checker algorithm rewrites in place.
bool CheckerAlgorithmHandlesFormal(FormalKind kind);

// §F.4.2.1 steps 3–5: for a reference to a formal input argument, the checker
// algorithm uses the same substitution shape as §F.4.1.1. Delegates to
// ReplaceFormalReference. `kind` shall be a kind the checker algorithm handles
// (i.e. not kLocalVariable).
ReferenceReplacement ReplaceCheckerFormalReference(FormalKind kind,
                                                   ActualNature actual);

// Scope across which §F.4.2.1 step 4's variable_lvalue prohibition applies.
enum class LvalueProhibitionScope {
  // §F.4.2.1 step 4: the whole checker. (Contrast §F.4.1.1, whose corresponding
  // prohibition is confined to the variable_lvalue of an operator_assignment or
  // inc_or_dec_expression in a sequence_match_item.)
  kWholeChecker,
};

// §F.4.2.1 step 4 shall: after step 4 replaces a typed non-matching formal
// input reference by a cast (item(t'(a_f)) or item(type(t)'(a_f))), that
// replaced reference shall not be a variable_lvalue anywhere in the checker. A
// cast expression is never an lvalue, so the rule forbids using such a formal
// as a variable_lvalue.
struct Step4LvalueRule {
  // Whether a step-4 replaced reference is permitted to be a variable_lvalue.
  // Always false: the cast it is replaced by cannot be an lvalue.
  bool replacement_may_be_lvalue = false;
  // The scope across which the prohibition is enforced.
  LvalueProhibitionScope scope = LvalueProhibitionScope::kWholeChecker;
};

// Returns the §F.4.2.1 step-4 variable_lvalue prohibition.
Step4LvalueRule CheckerStep4LvalueRule();

}  // namespace delta
