#include "simulator/checker_instance_scheduling.h"

namespace delta {

CheckerInstanceKind ClassifyCheckerInstance(
    bool instantiated_in_procedural_code) {
  return instantiated_in_procedural_code ? CheckerInstanceKind::kProcedural
                                         : CheckerInstanceKind::kStatic;
}

bool CheckerContentExistsEveryTimeStep(bool is_static_assertion_statement) {
  // §17.3: only the static assertion statements are exempt; every other content
  // of a checker instance exists during every time step.
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
  // §17.3: a nested static checker's static assertions belong to the parent, so
  // they follow the top-level ancestor's kind; otherwise the instance's own
  // kind applies.
  return nested_inside_another_checker ? top_level_ancestor_kind : own_kind;
}

}  // namespace delta
