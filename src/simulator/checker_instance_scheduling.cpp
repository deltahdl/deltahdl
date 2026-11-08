#include "simulator/checker_instance_scheduling.h"

namespace delta {

CheckerInstanceKind ClassifyCheckerInstance(
    bool instantiated_in_procedural_code) {
  return instantiated_in_procedural_code ? CheckerInstanceKind::kProcedural
                                         : CheckerInstanceKind::kStatic;
}

bool CheckerContentExistsEveryTimeStep(bool is_static_assertion_statement) {
  return !is_static_assertion_statement;
}

StaticAssertionTreatment TreatmentOfStaticConcurrentAssertion(
    CheckerInstanceKind kind) {
  switch (kind) {
    case CheckerInstanceKind::kStatic:
      return StaticAssertionTreatment::kMonitoredDirectly;
    case CheckerInstanceKind::kProcedural:
      return StaticAssertionTreatment::kAddedToPendingQueue;
  }
  return StaticAssertionTreatment::kMonitoredDirectly;
}

StaticAssertionTreatment TreatmentOfStaticDeferredAssertion(
    CheckerInstanceKind kind) {
  switch (kind) {
    case CheckerInstanceKind::kStatic:
      return StaticAssertionTreatment::kMonitoredDirectly;
    case CheckerInstanceKind::kProcedural:
      return StaticAssertionTreatment::kAddedToPendingQueue;
  }
  return StaticAssertionTreatment::kMonitoredDirectly;
}

CheckerInstanceKind EffectiveKindForStaticAssertions(
    CheckerInstanceKind own_kind, bool nested_inside_another_checker,
    CheckerInstanceKind top_level_ancestor_kind) {
  return nested_inside_another_checker ? top_level_ancestor_kind : own_kind;
}

}  // namespace delta
