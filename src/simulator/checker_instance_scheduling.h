#pragma once

#include <cstdint>

namespace delta {

// §17.3 describes how the contents of a checker instance behave during
// simulation, distinguishing static checker instances from procedural ones and
// prescribing how the static assertion statements inside a checker are
// scheduled. These helpers encode that runtime classification as pure functions
// so each rule can be observed in isolation.

// §17.3: a checker instantiation in procedural code is a procedural checker
// instance; a checker instantiation outside procedural code is a static checker
// instance.
enum class CheckerInstanceKind : uint8_t {
  kStatic,
  kProcedural,
};

// §17.3: classify a checker instance by where it is instantiated. Procedural
// code yields a procedural checker instance; anywhere else yields a static one.
CheckerInstanceKind ClassifyCheckerInstance(
    bool instantiated_in_procedural_code);

// §17.3: all contents of a checker instance other than its static assertion
// statements are considered to exist during every time step, regardless of
// whether the checker is static or procedural. Static assertion statements are
// the exception: they are instead treated as if they appear at the checker's
// instantiation point. Returns true for contents that exist every time step.
bool CheckerContentExistsEveryTimeStep(bool is_static_assertion_statement);

// §17.3: how a static assertion statement inside a checker is scheduled. In a
// static checker the assertion is monitored directly; in a procedural checker
// it is added to a pending queue (the pending procedural assertion queue for a
// concurrent assertion, the pending deferred assertion report for a deferred
// assertion) when the instantiation is reached in process execution.
enum class StaticAssertionTreatment : uint8_t {
  kMonitoredDirectly,
  kAddedToPendingQueue,
};

// §17.3: a static concurrent assertion in a static checker is continually
// monitored and begins execution on any time step matching its initial clock
// event; in a procedural checker it is added to the pending procedural
// assertion queue when the instantiation is reached in process execution.
StaticAssertionTreatment TreatmentOfStaticConcurrentAssertion(
    CheckerInstanceKind kind);

// §17.3: a static deferred assertion in a static checker is monitored whenever
// its expression changes; in a procedural checker it is added to the pending
// deferred assertion report when the instantiation is reached in process
// execution.
StaticAssertionTreatment TreatmentOfStaticDeferredAssertion(
    CheckerInstanceKind kind);

// §17.3: a static checker statically instantiated inside another checker has
// its static assertions treated as if instantiated in the parent checker, so
// they follow the instance kind of the top-level ancestor in the checker
// hierarchy rather than that of the nested instance. A checker that is not
// nested inside another checker is its own top-level ancestor.
CheckerInstanceKind EffectiveKindForStaticAssertions(
    CheckerInstanceKind own_kind, bool nested_inside_another_checker,
    CheckerInstanceKind top_level_ancestor_kind);

}  // namespace delta
