#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

namespace delta {
namespace {

struct DelayConstraint {
  std::size_t later = 0;
  std::size_t earlier = 0;
  int64_t gap = 0;
};

bool TakesNegativeDelays(const TimingCheckEntry& e) {
  return e.negative_timing_check_enabled &&
         (e.kind == TimingCheckKind::kSetuphold ||
          e.kind == TimingCheckKind::kRecrem);
}

int64_t& BeforeLimit(TimingCheckEntry& e) {
  return e.kind == TimingCheckKind::kRecrem ? e.signed_limit2 : e.signed_limit;
}

int64_t& AfterLimit(TimingCheckEntry& e) {
  return e.kind == TimingCheckKind::kRecrem ? e.signed_limit : e.signed_limit2;
}

void ReportLimitSum(const TimingCheckEntry& e, int64_t unit_ticks,
                    DiagEngine& diag) {
  const int64_t kSum = e.signed_limit + e.signed_limit2;
  if (kSum > unit_ticks) return;
  const bool kRecrem = e.kind == TimingCheckKind::kRecrem;
  diag.Error(
      e.loc,
      std::format("the limits of a {} with a negative limit sum to {} "
                  "in units of simulation precision, where more than 1 "
                  "is required",
                  kRecrem ? "$recrem" : "$setuphold",
                  static_cast<double>(kSum) / static_cast<double>(unit_ticks)),
      Subclause(kRecrem ? "31.3.6" : "31.3.3"));
}

std::size_t NodeOf(std::unordered_map<std::string, std::size_t>& nodes,
                   const std::string& name) {
  auto [it, added] = nodes.try_emplace(name, nodes.size());
  return it->second;
}

std::vector<DelayConstraint> ConstraintsOf(
    std::vector<TimingCheckEntry>& checks, int64_t unit_ticks,
    std::unordered_map<std::string, std::size_t>& nodes) {
  std::vector<DelayConstraint> constraints;
  for (TimingCheckEntry& e : checks) {
    if (!TakesNegativeDelays(e)) continue;
    const std::size_t kRef = NodeOf(nodes, e.inst_prefix + e.ref_signal);
    const std::size_t kData = NodeOf(nodes, e.inst_prefix + e.data_signal);
    if (BeforeLimit(e) != 0) {
      constraints.push_back({kRef, kData, unit_ticks - BeforeLimit(e)});
    }
    if (AfterLimit(e) != 0) {
      constraints.push_back({kData, kRef, unit_ticks - AfterLimit(e)});
    }
  }
  return constraints;
}

bool SolveLeastDelays(const std::vector<DelayConstraint>& constraints,
                      std::size_t count, std::vector<int64_t>& delays) {
  delays.assign(count, 0);
  for (std::size_t pass = 0; pass <= count; ++pass) {
    bool raised = false;
    for (const DelayConstraint& c : constraints) {
      if (delays[c.earlier] + c.gap <= delays[c.later]) continue;
      delays[c.later] = delays[c.earlier] + c.gap;
      raised = true;
    }
    if (!raised) return true;
  }
  return false;
}

void ZeroLeastNegativeLimit(std::vector<TimingCheckEntry>& checks,
                            DiagEngine& diag) {
  std::vector<int64_t*> places;
  std::vector<const TimingCheckEntry*> owners;
  std::vector<int64_t> limits;
  for (TimingCheckEntry& e : checks) {
    if (!TakesNegativeDelays(e)) continue;
    for (int64_t* place : {&BeforeLimit(e), &AfterLimit(e)}) {
      places.push_back(place);
      owners.push_back(&e);
      limits.push_back(*place);
    }
  }
  ZeroSmallestNegativeTimingLimit(limits);
  std::size_t i = 0;
  while (limits[i] == *places[i]) ++i;
  diag.Warning(owners[i]->loc,
               std::format("the negative timing check limits leave the "
                           "delayed signals no consistent delays; this "
                           "check's limit of {} is set to 0",
                           *places[i]),
               Subclause("31.9.1"));
  *places[i] = 0;
}

void ShiftLimit(uint64_t& limit, int64_t& signed_limit, int64_t shift,
                const SourceLoc& loc, DiagEngine& diag) {
  const AdjustedNegativeTimingLimit kAdjusted =
      ShiftTimingCheckLimit(limit, shift);
  if (kAdjusted.warn) {
    diag.Warning(loc,
                 "adjusted for the delays of the delayed signals it is "
                 "evaluated on, a limit of this check is no longer positive "
                 "and is set to 0",
                 Subclause("31.9.1"));
  }
  limit = kAdjusted.limit;
  signed_limit = static_cast<int64_t>(kAdjusted.limit);
}

void AdjustLimitsForDelays(TimingCheckEntry& e, int64_t shift,
                           DiagEngine& diag) {
  e.delayed_signal_shift = shift;
  if (e.kind == TimingCheckKind::kNochange) {
    e.start_edge_offset += shift;
    e.end_edge_offset -= shift;
    return;
  }
  const int64_t kFirstShift = FirstLimitDelayShift(e);
  ShiftLimit(e.limit, e.signed_limit, kFirstShift, e.loc, diag);
  ShiftLimit(e.limit2, e.signed_limit2, -kFirstShift, e.loc, diag);
}

}  // namespace

int64_t FirstLimitDelayShift(const TimingCheckEntry& check) {
  const bool kFirstBefore = check.kind == TimingCheckKind::kSetup ||
                            check.kind == TimingCheckKind::kSetuphold ||
                            check.kind == TimingCheckKind::kRemoval;
  return kFirstBefore ? check.delayed_signal_shift
                      : -check.delayed_signal_shift;
}

AdjustedNegativeTimingLimit ShiftTimingCheckLimit(uint64_t limit,
                                                  int64_t shift) {
  if (limit == 0) return {0u, false};
  return AdjustNegativeTimingCheckLimit(static_cast<int64_t>(limit) + shift);
}

bool EvaluatedOnDelayedSignals(const TimingCheckEntry& e) {
  return TimingCheckUsesDelayedSignals(e.kind) && !TakesNegativeDelays(e);
}

void SpecifyManager::ResolveNegativeTimingCheckDelays(int64_t unit_ticks,
                                                      DiagEngine& diag) {
  timing_check_signal_delays_.clear();
  for (const TimingCheckEntry& e : timing_checks_) {
    if (TakesNegativeDelays(e)) ReportLimitSum(e, unit_ticks, diag);
  }
  std::unordered_map<std::string, std::size_t> nodes;
  std::vector<int64_t> delays;
  for (;;) {
    std::vector<DelayConstraint> constraints =
        ConstraintsOf(timing_checks_, unit_ticks, nodes);
    if (SolveLeastDelays(constraints, nodes.size(), delays)) break;
    ZeroLeastNegativeLimit(timing_checks_, diag);
  }
  for (const auto& [name, node] : nodes) {
    if (delays[node] > 0) {
      timing_check_signal_delays_[name] = static_cast<uint64_t>(delays[node]);
    }
  }
  for (TimingCheckEntry& e : timing_checks_) {
    if (!EvaluatedOnDelayedSignals(e)) continue;
    const int64_t kShift = DelayedSignalShift(e);
    if (kShift != 0) AdjustLimitsForDelays(e, kShift, diag);
  }
}

uint64_t SpecifyManager::TimingCheckSignalDelay(std::string_view signal) const {
  auto it = timing_check_signal_delays_.find(std::string(signal));
  return it == timing_check_signal_delays_.end() ? 0 : it->second;
}

int64_t SpecifyManager::DelayedSignalShift(
    const TimingCheckEntry& check) const {
  if (check.kind == TimingCheckKind::kWidth ||
      check.kind == TimingCheckKind::kPeriod) {
    return 0;
  }
  return static_cast<int64_t>(
             TimingCheckSignalDelay(check.inst_prefix + check.ref_signal)) -
         static_cast<int64_t>(
             TimingCheckSignalDelay(check.inst_prefix + check.data_signal));
}

}  // namespace delta
