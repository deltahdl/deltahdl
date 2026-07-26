#pragma once

#include <cstdint>
#include <string>

#include "parser/ast.h"
#include "simulator/specify.h"

namespace delta {

// A single observed reference/data transition pair to test against the timing
// checks (IEEE 1800 §31): the reference event (signal + time) and the data
// event (signal + time) that together describe one timing-check observation.
struct TimingCheckEvent {
  std::string_view ref;
  uint64_t ref_time;
  std::string_view data;
  uint64_t data_time;
};

// Selects which TimingCheckEntry limit applies on each side of the reference
// time for two-sided checks (recrem / setuphold): `lower` is compared when the
// data event is on/before the reference, `upper` when it is after.
struct TwoSidedLimitSelector {
  uint64_t TimingCheckEntry::* lower;
  uint64_t TimingCheckEntry::* upper;
};

bool CheckTimingViolation(const std::vector<TimingCheckEntry>& timing_checks,
                          TimingCheckKind kind, const TimingCheckEvent& event,
                          const TwoSidedLimitSelector& selector);
void DerivePulseLimitsFromDelays(const uint64_t (&delays)[12],
                                 uint8_t reject_pct, uint8_t error_pct,
                                 uint64_t (&reject_limit)[12],
                                 uint64_t (&error_limit)[12]);
std::string SpecifyConditionText(const Expr* cond);

}  // namespace delta
