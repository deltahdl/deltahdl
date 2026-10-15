// §31.9.1 (printed pages 920-922): a negative $setuphold or $recrem is
// evaluated on delayed copies of its reference and data signals. Each signal
// has one delayed copy whichever checks name it, and the delays shift every
// check's window onto its delayed reference edge. The adjusted limits are the
// declared ones moved by the two delays: the limit bounding the side before the
// edge grows by the reference's delay and shrinks by the data's, and the limit
// bounding the side after it the other way round.
//
// The clause states no formula for the delays. Figure 31-6 (printed page 923)
// works three checks on a 10 ps precision to dCP 10.01, dD 0, dTI 20.02 and dTE
// 2.02, which are the least delays that leave every non-zero limit of every
// check, adjusted, at least one unit of precision. That is what is solved here:
// each such limit is a difference constraint between two delays, and the least
// non-negative solution is the longest path to each signal. One unit is also
// what §31.3.3 and §31.3.6 ask a negative check's two limits to sum to more
// than, which is exactly when one check's own two constraints can both hold.
//
// Limits no delays satisfy are what the clause calls mutually inconsistent. The
// run warns, sets the least negative limit to 0 and solves again, until a
// solution is reached; at worst every negative limit is 0 and nothing lags.

#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

namespace delta {
namespace {

// d[later] - d[earlier] >= gap, in ticks of the global precision.
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

// $setuphold's setup limit and $recrem's removal limit bound the side before
// the reference edge, and the declaration writes them first and second.
int64_t& BeforeLimit(TimingCheckEntry& e) {
  return e.kind == TimingCheckKind::kRecrem ? e.signed_limit2 : e.signed_limit;
}

int64_t& AfterLimit(TimingCheckEntry& e) {
  return e.kind == TimingCheckKind::kRecrem ? e.signed_limit : e.signed_limit2;
}

// §31.3.3 and §31.3.6: with a limit negative, the two sum to more than one
// unit of simulation precision, which is one tick.
void ReportLimitSum(const TimingCheckEntry& e, DiagEngine& diag) {
  const int64_t kSum = e.signed_limit + e.signed_limit2;
  if (kSum > 1) return;
  const bool kRecrem = e.kind == TimingCheckKind::kRecrem;
  diag.Error(e.loc,
             std::format("the limits of a {} with a negative limit sum to {} "
                         "in units of simulation precision, where more than 1 "
                         "is required",
                         kRecrem ? "$recrem" : "$setuphold", kSum),
             Subclause(kRecrem ? "31.3.6" : "31.3.3"));
}

std::size_t NodeOf(std::unordered_map<std::string, std::size_t>& nodes,
                   const std::string& name) {
  auto [it, added] = nodes.try_emplace(name, nodes.size());
  return it->second;
}

// A limit L adjusted by the two delays stays at least one tick: before the
// edge L + d(ref) - d(data) >= 1, after it L - d(ref) + d(data) >= 1. A zero
// limit bounds no window on its side and constrains nothing.
std::vector<DelayConstraint> ConstraintsOf(
    std::vector<TimingCheckEntry>& checks,
    std::unordered_map<std::string, std::size_t>& nodes) {
  std::vector<DelayConstraint> constraints;
  for (TimingCheckEntry& e : checks) {
    if (!TakesNegativeDelays(e)) continue;
    const std::size_t kRef = NodeOf(nodes, e.inst_prefix + e.ref_signal);
    const std::size_t kData = NodeOf(nodes, e.inst_prefix + e.data_signal);
    if (BeforeLimit(e) != 0) {
      constraints.push_back({kRef, kData, 1 - BeforeLimit(e)});
    }
    if (AfterLimit(e) != 0) {
      constraints.push_back({kData, kRef, 1 - AfterLimit(e)});
    }
  }
  return constraints;
}

// The least non-negative delays meeting every constraint, which is the
// longest path to each signal. A pass that still raises a delay after as many
// passes as there are signals is on a cycle that raises it without end, and
// then there is no solution.
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

// Sets the least negative limit of the negative checks to 0, with §31.9.1's
// warning at its check. Limits with none negative always solve, every delay
// at 0 leaving each non-zero limit as it was and so at least one tick, so the
// caller asks this only where some limit is negative.
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

}  // namespace

void SpecifyManager::ResolveNegativeTimingCheckDelays(DiagEngine& diag) {
  timing_check_signal_delays_.clear();
  for (const TimingCheckEntry& e : timing_checks_) {
    if (TakesNegativeDelays(e)) ReportLimitSum(e, diag);
  }
  std::unordered_map<std::string, std::size_t> nodes;
  std::vector<int64_t> delays;
  for (;;) {
    std::vector<DelayConstraint> constraints =
        ConstraintsOf(timing_checks_, nodes);
    if (SolveLeastDelays(constraints, nodes.size(), delays)) break;
    ZeroLeastNegativeLimit(timing_checks_, diag);
  }
  for (const auto& [name, node] : nodes) {
    if (delays[node] > 0) {
      timing_check_signal_delays_[name] = static_cast<uint64_t>(delays[node]);
    }
  }
}

uint64_t SpecifyManager::TimingCheckSignalDelay(std::string_view signal) const {
  auto it = timing_check_signal_delays_.find(std::string(signal));
  return it == timing_check_signal_delays_.end() ? 0 : it->second;
}

}  // namespace delta
