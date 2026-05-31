#pragma once

#include <cstdint>

namespace delta {

// §17.3 governs how a checker is instantiated. A checker may be instantiated
// wherever a concurrent assertion may appear (see §16.14), subject to the
// placement, argument, and connection rules collected below. These helpers
// encode those rules as small pure predicates so the legality of an individual
// checker instantiation can be decided in isolation.

// §17.3: the syntactic site at which a checker instantiation appears. A
// concurrent-assertion context is the general case where instantiation is
// permitted; the remaining sites are the placements §17.3 singles out as
// illegal exceptions.
enum class CheckerInstantiationSite : uint8_t {
  kConcurrentAssertionContext,
  kForkJoin,
  kForkJoinAny,
  kForkJoinNone,
  kProcedureOfAnotherChecker,
};

// §17.3: a checker may be instantiated wherever a concurrent assertion may
// appear, with two exceptions. It is illegal inside a fork-join,
// fork-join_any, or fork-join_none block, and it is illegal inside a procedure
// of another checker.
bool CheckerInstantiationSiteIsLegal(CheckerInstantiationSite site);

// §17.3: an actual argument bound to an output formal of a checker. Each such
// actual argument shall be a variable lvalue or a net lvalue; any other form is
// rejected.
enum class CheckerOutputActualArg : uint8_t {
  kVariableLvalue,
  kNetLvalue,
  kOther,
};

// §17.3: each checker actual output argument shall be a variable_lvalue or a
// net_lvalue.
bool CheckerOutputActualArgIsLegal(CheckerOutputActualArg arg);

// §17.3: the connection styles a checker instantiation may use to bind formal
// arguments to actual arguments, paralleling module ports (see §23.3.2).
enum class CheckerPortConnectionStyle : uint8_t {
  kPositional,
  kNamedExplicit,
  kNamedImplicit,
  kWildcard,
};

// §17.3: checker formal arguments may be connected to their actual arguments in
// ways similar to module ports — positional order, fully explicit named
// connections, implicit named connections, and a wildcard port name. Every one
// of these four styles is supported.
bool IsSupportedCheckerPortConnectionStyle(CheckerPortConnectionStyle style);

// §17.3: when the terminal `$` is an actual input argument to a checker
// instance, each reference of the corresponding formal must be one of these
// permitted uses. Any other use of the formal makes the `$` argument illegal.
enum class DollarFormalReferenceUse : uint8_t {
  kCycleDelayRangeUpperBound,
  kSequenceInstanceActual,
  kPropertyInstanceActual,
  kCheckerInstanceActual,
  kNestedCheckerDefaultArg,
  kOther,
};

// §17.3: a reference to a formal bound to `$` is legal only when it acts
// as an upper bound in a cycle_delay_const_range_expression, or is itself an
// actual argument to a named sequence instance, a named property instance, or a
// checker instance, or is a default argument to a nested checker.
bool DollarFormalReferenceIsLegal(DollarFormalReferenceUse use);

// §17.3: if `$` is an actual input argument to a checker instance, the
// corresponding formal argument shall be untyped and every reference of that
// formal shall be one of the permitted uses (see DollarFormalReferenceIsLegal).
bool DollarActualArgumentIsLegal(bool formal_is_untyped,
                                 bool all_formal_references_permitted);

// §17.3: if an actual input argument contains any subexpression that is a const
// cast or an automatic value taken from procedural code, then the corresponding
// formal argument shall not be used in a continuous assignment or in the
// procedural code within the checker.
bool ConstCastOrAutomaticActualFormalUsageIsLegal(
    bool actual_has_const_cast_or_automatic_value,
    bool formal_used_in_continuous_assignment,
    bool formal_used_in_procedural_code);

}  // namespace delta
