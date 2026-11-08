#pragma once

#include <cstdint>

namespace delta {

enum class CheckerInstanceKind : uint8_t {
  kStatic,
  kProcedural,
};

CheckerInstanceKind ClassifyCheckerInstance(
    bool instantiated_in_procedural_code);

bool CheckerContentExistsEveryTimeStep(bool is_static_assertion_statement);

enum class StaticAssertionTreatment : uint8_t {
  kMonitoredDirectly,
  kAddedToPendingQueue,
};

StaticAssertionTreatment TreatmentOfStaticConcurrentAssertion(
    CheckerInstanceKind kind);

StaticAssertionTreatment TreatmentOfStaticDeferredAssertion(
    CheckerInstanceKind kind);

CheckerInstanceKind EffectiveKindForStaticAssertions(
    CheckerInstanceKind own_kind, bool nested_inside_another_checker,
    CheckerInstanceKind top_level_ancestor_kind);

}  // namespace delta
