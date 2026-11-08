#pragma once

#include <string_view>

namespace delta {

bool TriggeredEndingClockMatchesContext(std::string_view ending_clock,
                                        std::string_view context_clock);

bool MatchedDetectsCrossClockEndPoint(std::string_view source_clock,
                                      std::string_view destination_clock);

bool MatchedAllowedOnSequenceWithFormalArguments();

bool MatchedLocalVariableRulesSameAsTriggered();

bool MatchedMultipleMatchesTreatedAsOrDisjuncts();

bool MatchedSynchronizesAcrossClocks();

}  // namespace delta
