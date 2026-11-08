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

struct TimingCheckEvent {
  std::string_view ref;
  uint64_t ref_time;
  std::string_view data;
  uint64_t data_time;
};

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
void ReplacePathDelayRetaining(PathDelay& existing, PathDelay replacement,
                               const PathDelayRetention& retain);
std::string SpecifyConditionText(const Expr* cond);
std::string SpecifyTerminalName(const SpecifyTerminal& t);
TerminalSelect SpecifyTerminalSelect(const SpecifyTerminal& t, SimContext& ctx,
                                     Arena& arena);
bool SpecifyConditionsMatch(std::string_view a, std::string_view b);

}  // namespace delta
