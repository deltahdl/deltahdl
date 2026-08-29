#pragma once

#include <cstdint>
#include <string>
#include <string_view>

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

// Which of a two-sided check's two declared limits bounds the side of the
// reference time a data event before it falls on.
//
// §31.3.3's Table 31-3 gives $setuphold's setup_limit the reference_event role
// and its hold_limit the data_event role, and Syntax 31-5 writes setup first,
// so its first declared limit bounds the earlier side. §31.3.6's Table 31-6
// gives $recrem's removal_limit the reference_event role and its recovery_limit
// the data_event role, and Syntax 31-8 writes recovery first, so its second
// declared limit does.
//
// One value settles both paths CheckTimingViolation takes: the unsigned pair a
// check compares elapsed time against, and the signed pair §31.9.1's window is
// built from. Stating the two separately is what let them disagree, which is
// issue #3419 -- the unsigned path read the order its caller passed and the
// signed one read the declaration order for every kind.
enum class TwoSidedLimitOrder : uint8_t {
  kFirstBoundsBefore,
  kSecondBoundsBefore,
};

bool CheckTimingViolation(const std::vector<TimingCheckEntry>& timing_checks,
                          TimingCheckKind kind, const TimingCheckEvent& event,
                          TwoSidedLimitOrder order);
void DerivePulseLimitsFromDelays(const uint64_t (&delays)[12],
                                 uint8_t reject_pct, uint8_t error_pct,
                                 uint64_t (&reject_limit)[12],
                                 uint64_t (&error_limit)[12]);
std::string SpecifyConditionText(const Expr* cond);
bool SpecifyConditionsMatch(std::string_view a, std::string_view b);

}  // namespace delta
