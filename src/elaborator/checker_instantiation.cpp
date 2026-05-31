#include "elaborator/checker_instantiation.h"

namespace delta {

bool CheckerInstantiationSiteIsLegal(CheckerInstantiationSite site) {
  switch (site) {
    case CheckerInstantiationSite::kConcurrentAssertionContext:
      return true;
    // §17.3: instantiating a checker in a fork-join, fork-join_any, or
    // fork-join_none block is illegal.
    case CheckerInstantiationSite::kForkJoin:
    case CheckerInstantiationSite::kForkJoinAny:
    case CheckerInstantiationSite::kForkJoinNone:
    // §17.3: instantiating a checker in a procedure of another checker is
    // illegal.
    case CheckerInstantiationSite::kProcedureOfAnotherChecker:
      return false;
  }
  return false;
}

bool CheckerOutputActualArgIsLegal(CheckerOutputActualArg arg) {
  switch (arg) {
    case CheckerOutputActualArg::kVariableLvalue:
    case CheckerOutputActualArg::kNetLvalue:
      return true;
    case CheckerOutputActualArg::kOther:
      return false;
  }
  return false;
}

bool IsSupportedCheckerPortConnectionStyle(CheckerPortConnectionStyle style) {
  switch (style) {
    case CheckerPortConnectionStyle::kPositional:
    case CheckerPortConnectionStyle::kNamedExplicit:
    case CheckerPortConnectionStyle::kNamedImplicit:
    case CheckerPortConnectionStyle::kWildcard:
      return true;
  }
  return false;
}

bool DollarFormalReferenceIsLegal(DollarFormalReferenceUse use) {
  switch (use) {
    case DollarFormalReferenceUse::kCycleDelayRangeUpperBound:
    case DollarFormalReferenceUse::kSequenceInstanceActual:
    case DollarFormalReferenceUse::kPropertyInstanceActual:
    case DollarFormalReferenceUse::kCheckerInstanceActual:
    case DollarFormalReferenceUse::kNestedCheckerDefaultArg:
      return true;
    case DollarFormalReferenceUse::kOther:
      return false;
  }
  return false;
}

bool DollarActualArgumentIsLegal(bool formal_is_untyped,
                                 bool all_formal_references_permitted) {
  // §17.3: the formal bound to `$` must be untyped, and all of its references
  // must be permitted uses. Both conditions are required.
  return formal_is_untyped && all_formal_references_permitted;
}

bool ConstCastOrAutomaticActualFormalUsageIsLegal(
    bool actual_has_const_cast_or_automatic_value,
    bool formal_used_in_continuous_assignment,
    bool formal_used_in_procedural_code) {
  // §17.3: the restriction applies only when the actual argument carries a
  // const cast or an automatic value from procedural code. When it does, the
  // formal may not appear in a continuous assignment or in the checker's
  // procedural code.
  if (!actual_has_const_cast_or_automatic_value) return true;
  return !formal_used_in_continuous_assignment &&
         !formal_used_in_procedural_code;
}

}  // namespace delta
