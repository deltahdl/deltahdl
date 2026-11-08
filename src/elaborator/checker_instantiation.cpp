#include "elaborator/checker_instantiation.h"

namespace delta {

bool CheckerInstantiationSiteIsLegal(CheckerInstantiationSite site) {
  switch (site) {
    case CheckerInstantiationSite::kConcurrentAssertionContext:
      return true;
    case CheckerInstantiationSite::kForkJoin:
    case CheckerInstantiationSite::kForkJoinAny:
    case CheckerInstantiationSite::kForkJoinNone:
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
  return formal_is_untyped && all_formal_references_permitted;
}

bool ConstCastOrAutomaticActualFormalUsageIsLegal(
    bool actual_has_const_cast_or_automatic_value,
    bool formal_used_in_continuous_assignment,
    bool formal_used_in_procedural_code) {
  if (!actual_has_const_cast_or_automatic_value) return true;
  return !formal_used_in_continuous_assignment &&
         !formal_used_in_procedural_code;
}

}  // namespace delta
