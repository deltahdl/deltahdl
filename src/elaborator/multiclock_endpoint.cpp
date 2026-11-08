#include "elaborator/multiclock_endpoint.h"

#include <string_view>

#include "elaborator/sequence_method.h"

namespace delta {

bool TriggeredEndingClockMatchesContext(std::string_view ending_clock,
                                        std::string_view context_clock) {
  return ending_clock == context_clock;
}

bool MatchedDetectsCrossClockEndPoint(std::string_view source_clock,
                                      std::string_view destination_clock) {
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
