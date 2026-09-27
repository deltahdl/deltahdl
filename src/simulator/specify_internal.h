#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"

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
// Overwrites `existing` with `replacement`, holding back whichever pulse
// (reject/error) limits `retain` names at the values `existing` already had.
// Defined in specify.cpp.
void ReplacePathDelayPreservingPulse(PathDelay& existing, PathDelay replacement,
                                     PathDelayPulseRetention retain);
std::string SpecifyConditionText(const Expr* cond);
// The name a specify terminal reads in its module: the port identifier, or
// `interface_identifier . port_identifier` spelled with its dot (§30.4.2,
// §31.2 Syntax 31-2, A.7.3). Defined in specify_register.cpp.
std::string SpecifyTerminalName(const SpecifyTerminal& t);
// The select `t` was written with, its bounds evaluated; an indexed
// part-select, `a[i +: 2]`, is given as the part it covers. Defined in
// specify_register.cpp.
TerminalSelect SpecifyTerminalSelect(const SpecifyTerminal& t, SimContext& ctx,
                                     Arena& arena);
bool SpecifyConditionsMatch(std::string_view a, std::string_view b);

}  // namespace delta
