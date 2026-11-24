#include <gtest/gtest.h>

#include "helpers_multiclock_counts.h"

using namespace delta;

namespace {

TEST(RepetitionOfAClockedSequenceSim,
     AnUnboundedRepetitionOnTheClockInForceIsTheUnclockedGroup) {
  ExpectAsWithoutTheRedundantClock("(@(posedge clk0) sig0 ##1 1)[*1:$]",
                                   "(sig0 ##1 1)[*1:$]");
  ExpectAsWithoutTheRedundantClock("(@(posedge clk0) sig0 ##1 1)[+]",
                                   "(sig0 ##1 1)[+]");
  ExpectAsWithoutTheRedundantClock("(@(posedge clk0) sig0 ##1 1)[*] ##1 sig1",
                                   "(sig0 ##1 1)[*] ##1 sig1");
}

}  // namespace
