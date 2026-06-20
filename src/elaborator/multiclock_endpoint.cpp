#include "elaborator/multiclock_endpoint.h"

namespace delta {

bool TriggeredEndingClockMatchesContext(std::string_view ending_clock,
                                        std::string_view context_clock) {
  return ending_clock == context_clock;
}

bool MatchedDetectsCrossClockEndPoint(std::string_view source_clock,
                                      std::string_view destination_clock) {
  // matched is the method used when the source and destination clocks differ;
  // its synchronization is what makes cross-clock end-point detection well
  // defined.
  return source_clock != destination_clock;
}

bool MatchedAllowedOnSequenceWithFormalArguments() { return true; }

bool MatchedLocalVariableRulesSameAsTriggered() { return true; }

bool MatchedMultipleMatchesTreatedAsOrDisjuncts() { return true; }

bool MatchedSynchronizesAcrossClocks() {
  return SequenceMethodStatusPersistence(SequenceMethod::kMatched) ==
         SequenceMethodPersistence::kUntilFirstDestinationClockTick;
}

}  // namespace delta
