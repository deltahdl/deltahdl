#pragma once

#include <cstdint>

namespace delta {

enum class CheckerInstantiationSite : uint8_t {
  kConcurrentAssertionContext,
  kForkJoin,
  kForkJoinAny,
  kForkJoinNone,
  kProcedureOfAnotherChecker,
};

bool CheckerInstantiationSiteIsLegal(CheckerInstantiationSite site);

enum class CheckerOutputActualArg : uint8_t {
  kVariableLvalue,
  kNetLvalue,
  kOther,
};

bool CheckerOutputActualArgIsLegal(CheckerOutputActualArg arg);

enum class CheckerPortConnectionStyle : uint8_t {
  kPositional,
  kNamedExplicit,
  kNamedImplicit,
  kWildcard,
};

bool IsSupportedCheckerPortConnectionStyle(CheckerPortConnectionStyle style);

enum class DollarFormalReferenceUse : uint8_t {
  kCycleDelayRangeUpperBound,
  kSequenceInstanceActual,
  kPropertyInstanceActual,
  kCheckerInstanceActual,
  kNestedCheckerDefaultArg,
  kOther,
};

bool DollarFormalReferenceIsLegal(DollarFormalReferenceUse use);

bool DollarActualArgumentIsLegal(bool formal_is_untyped,
                                 bool all_formal_references_permitted);

bool ConstCastOrAutomaticActualFormalUsageIsLegal(
    bool actual_has_const_cast_or_automatic_value,
    bool formal_used_in_continuous_assignment,
    bool formal_used_in_procedural_code);

}  // namespace delta
