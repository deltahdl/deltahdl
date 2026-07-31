#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/variable.h"

namespace delta {

// True when any expression of `exprs` reads one of the changed specparams.
template <typename Exprs>
static bool AnyExprReadsSpecparam(const Exprs& exprs,
                                  const std::vector<std::string>& changed) {
  for (const Expr* e : exprs) {
    if (ExprReadsSpecparam(e, changed)) return true;
  }
  return false;
}

// §32.4.3: a module path delay is an expression containing specparams, and it
// was already reduced to a number when the path was declared, so a path whose
// delay reads the changed specparam is recomputed from its declaration. A path
// that reads nothing new is left exactly as it stands: recomputing it would
// discard whatever else had been annotated onto it.
void SpecifyManager::RebuildPathDelaysForSpecparam(
    const std::vector<std::string>& changed) {
  for (const auto* decl : path_decls_) {
    if (!AnyExprReadsSpecparam(decl->delays, changed)) continue;
    AddPathDelay(
        BuildPathDelayFromDecl(*decl, *specparam_ctx_, *specparam_arena_),
        /*preserve_pulse_limits=*/true);
  }
}

// §32.4.3: the rule reaches every expression containing the specparam, not only
// module path delays. A timing check's constraint limits are written as
// expressions as well, and they were likewise reduced to numbers when the check
// was declared, so a check whose limit reads the changed specparam is rebuilt
// from its declaration too.
void SpecifyManager::RebuildTimingChecksForSpecparam(
    const std::vector<std::string>& changed) {
  for (const auto* decl : timing_check_decls_) {
    if (!AnyExprReadsSpecparam(decl->limits, changed)) continue;
    AddTimingCheck(BuildTimingCheckUnderOptions(
        *decl, *specparam_ctx_, *specparam_arena_, timing_check_options_));
  }
}

// Overwrite the driver already recorded for each output the rebuilt gate
// drives, so a DEVICE delay still finds one entry per output rather than a
// stale one beside a fresh one.
void SpecifyManager::ReplacePrimitiveDriver(PrimitiveDriver rebuilt) {
  for (auto& existing : primitive_drivers_) {
    if (existing.output_port == rebuilt.output_port) {
      existing = std::move(rebuilt);
      return;
    }
  }
  primitive_drivers_.push_back(std::move(rebuilt));
}

// §32.4.3: a gate primitive's declared propagation delay is an expression as
// well, and it too was reduced to numbers when the gate's drivers were
// registered. A gate whose delay expression reads the changed specparam is
// rebuilt from its declaration.
void SpecifyManager::RebuildGateDriversForSpecparam(
    const std::vector<std::string>& changed) {
  for (const auto* gate : gate_decls_) {
    const Expr* const kDelays[3] = {gate->gate_delay, gate->gate_delay_fall,
                                    gate->gate_delay_decay};
    if (!AnyExprReadsSpecparam(kDelays, changed)) continue;
    for (auto& rebuilt : BuildPrimitiveDriversFromGate(*gate, *specparam_ctx_,
                                                       *specparam_arena_)) {
      ReplacePrimitiveDriver(std::move(rebuilt));
    }
  }
}

void SpecifyManager::ApplyAnnotatedSpecparam(const std::string& name,
                                             uint64_t value) {
  if (specparam_ctx_ == nullptr) return;
  // §32.4.3: a LABEL section annotates to specparams. A name the module did not
  // declare as a specparam therefore has nothing here for the annotation to
  // land on, whatever else the design may happen to call by that name.
  if (!IsDeclaredSpecparam(name)) return;

  if (Variable* storage = specparam_ctx_->FindVariable(name);
      storage != nullptr) {
    const uint32_t kWidth =
        storage->value.width == 0 ? 32u : storage->value.width;
    storage->value = MakeLogic4VecVal(*specparam_arena_, kWidth, value);
  }

  // §32.4.3: an expression containing one or more specparams is reevaluated
  // when a value is annotated to it from an SDF file.
  const std::vector<std::string> kChanged{name};
  RebuildPathDelaysForSpecparam(kChanged);
  RebuildTimingChecksForSpecparam(kChanged);
  RebuildGateDriversForSpecparam(kChanged);
}

void SpecifyManager::SetSpecparamValue(SpecparamValue spec) {
  std::string name = spec.name;
  uint64_t value = spec.value;
  auto it = specparam_index_.find(spec.name);
  if (it != specparam_index_.end()) {
    specparam_values_[it->second] = std::move(spec);
  } else {
    specparam_index_[spec.name] = specparam_values_.size();
    specparam_values_.push_back(std::move(spec));
  }

  ApplyAnnotatedSpecparam(name, value);

  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(value);
  }
}

void SpecifyManager::IncrementSpecparamValue(SpecparamValue delta) {
  std::string name = std::move(delta.name);
  uint64_t added = delta.value;
  uint64_t new_value = added;
  auto it = specparam_index_.find(name);
  if (it != specparam_index_.end()) {
    new_value = specparam_values_[it->second].value + added;
    specparam_values_[it->second].value = new_value;
  } else {
    specparam_index_[name] = specparam_values_.size();
    SpecparamValue stored;
    stored.name = name;
    stored.value = added;
    specparam_values_.push_back(std::move(stored));
  }
  ApplyAnnotatedSpecparam(name, new_value);
  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(new_value);
  }
}

void SpecifyManager::RegisterSpecparamReevaluation(
    std::string name, std::function<void(uint64_t)> reevaluate) {
  specparam_reevaluators_.emplace_back(std::move(name), std::move(reevaluate));
}

namespace {

void ApplySdfPercentPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                                uint64_t error) {
  uint64_t reject_pct = reject;
  uint64_t error_pct = has_error ? error : reject;
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

void ClampPulseLimitsToDelays(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    if (pd.reject_limit[i] > pd.delays[i]) pd.reject_limit[i] = pd.delays[i];
    if (pd.error_limit[i] > pd.delays[i]) pd.error_limit[i] = pd.delays[i];
  }
}

// A limit a construct states outright is a pulse width, and no pulse is
// narrower than none at all, so a value written below zero reads as zero.
uint64_t StatedPulseLimit(int64_t value) {
  return value < 0 ? 0U : static_cast<uint64_t>(value);
}

// §32.7: the two amounts one transition slot's limits are changed by. A
// percentage entry states a fraction of that slot's own delay, so what it adds
// differs from slot to slot; a plain entry states the amount directly. An entry
// carrying no error value uses its reject value for both limits, the same way
// one stating the limits outright does.
struct SlotPulseLimitDeltas {
  int64_t reject;
  int64_t error;
};

SlotPulseLimitDeltas PulseLimitDeltasForSlot(const SdfPulseLimitSpec& spec,
                                             uint64_t delay) {
  const int64_t kReject = spec.reject;
  const int64_t kError = spec.has_error ? spec.error : spec.reject;
  if (!spec.is_percent) return SlotPulseLimitDeltas{kReject, kError};
  const auto kDelay = static_cast<int64_t>(delay);
  return SlotPulseLimitDeltas{kReject * kDelay / 100, kError * kDelay / 100};
}

// §32.7: a limit the amount would carry below zero is left at zero instead.
uint64_t AddPulseLimitDelta(uint64_t limit, int64_t delta) {
  const int64_t kMoved = static_cast<int64_t>(limit) + delta;
  return kMoved < 0 ? 0U : static_cast<uint64_t>(kMoved);
}

// §32.7: add the entry's amounts to what the path already holds, slot by slot.
void IncrementPulseLimitsOnPath(PathDelay& pd, const SdfPulseLimitSpec& spec) {
  for (int i = 0; i < 12; ++i) {
    const SlotPulseLimitDeltas kDeltas =
        PulseLimitDeltasForSlot(spec, pd.delays[i]);
    pd.reject_limit[i] = AddPulseLimitDelta(pd.reject_limit[i], kDeltas.reject);
    pd.error_limit[i] = AddPulseLimitDelta(pd.error_limit[i], kDeltas.error);
  }
}

// §32.7: put one entry's limits on a path it reaches. The entry either states
// the limits or states amounts to change them by, and either way the limits it
// leaves behind are measured against the path's delay afterwards -- a limit
// this construct puts above the delay behaves as one put at the delay.
void PlaceSdfPulseLimits(PathDelay& pd, const SdfPulseLimitSpec& spec) {
  if (spec.is_increment) {
    IncrementPulseLimitsOnPath(pd, spec);
  } else if (spec.is_percent) {
    ApplySdfPercentPulseLimits(pd, StatedPulseLimit(spec.reject),
                               spec.has_error, StatedPulseLimit(spec.error));
  } else {
    ApplySdfPulseLimits(pd, StatedPulseLimit(spec.reject), spec.has_error,
                        StatedPulseLimit(spec.error));
  }
  ClampPulseLimitsToDelays(pd);
}

}  // namespace

void SpecifyManager::AddSdfPulseLimit(const SdfPulseLimitSpec& spec) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != spec.src || pd.dst_port != spec.dst) continue;
    PlaceSdfPulseLimits(pd, spec);
  }
}

void SpecifyManager::ResolvePulseControlSpecparams(
    const std::vector<PulseControlSpecparam>& specs) {
  // §30.7.1 precedence: apply every non-path-specific PATHPULSE$ first so it
  // reaches all module paths, then let each path-specific PATHPULSE$in$out
  // override the path it names. Because the path-specific pass runs second, it
  // always wins for the paths it names no matter where the module-wide
  // specparam appeared in source. A path-specific specparam that names no
  // existing path (e.g. a non-first terminal of a multiple-path declaration)
  // matches nothing and is thereby ignored.
  for (const auto& s : specs) {
    if (!s.input.empty() || !s.output.empty()) continue;
    for (auto& pd : path_delays_) {
      ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
    }
  }
  for (const auto& s : specs) {
    if (s.input.empty() && s.output.empty()) continue;
    ApplyPathSpecificPulseControl(s);
  }
}

// §30.7.1: a path-specific PATHPULSE$in$out overrides only the path it names. A
// specparam that names no existing path (e.g. a non-first terminal of a
// multiple-path declaration) matches nothing and is thereby ignored.
void SpecifyManager::ApplyPathSpecificPulseControl(
    const PulseControlSpecparam& s) {
  for (auto& pd : path_delays_) {
    if (s.input == std::string_view(pd.src_port) &&
        s.output == std::string_view(pd.dst_port)) {
      ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
    }
  }
}

void SpecifyManager::IncrementSdfPulseLimit(std::string_view src,
                                            std::string_view dst,
                                            int64_t reject_delta,
                                            int64_t error_delta) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    for (int i = 0; i < 12; ++i) {
      const int64_t kNewReject =
          static_cast<int64_t>(pd.reject_limit[i]) + reject_delta;
      const int64_t kNewError =
          static_cast<int64_t>(pd.error_limit[i]) + error_delta;
      pd.reject_limit[i] =
          kNewReject < 0 ? 0u : static_cast<uint64_t>(kNewReject);
      pd.error_limit[i] = kNewError < 0 ? 0u : static_cast<uint64_t>(kNewError);
    }
  }
}

void SpecifyManager::SetGlobalPulseLimitPercents(uint8_t reject_pct,
                                                 uint8_t error_pct) {
  reject_pulse_pct_ = reject_pct;
  error_pulse_pct_ = error_pct;
}

void SpecifyManager::SetPathOutputPulseStyle(std::string output,
                                             PulseStyle style) {
  path_output_pulse_styles_[std::move(output)] = style;
}

void SpecifyManager::SetGlobalPulseStyle(PulseStyle style) {
  has_global_pulse_style_ = true;
  global_pulse_style_ = style;
}

PulseStyle SpecifyManager::ResolvePulseStyle(std::string_view output) const {
  // The invocation option, when present, overrides every specify block
  // declaration.
  if (has_global_pulse_style_) return global_pulse_style_;
  auto it = path_output_pulse_styles_.find(std::string(output));
  if (it != path_output_pulse_styles_.end()) return it->second;
  // Absent both, the default filtering style is on-event.
  return PulseStyle::kOnEvent;
}

void SpecifyManager::SetPathOutputShowCancelled(std::string output,
                                                ShowCancelled mode) {
  path_output_showcancelled_[std::move(output)] = mode;
}

void SpecifyManager::SetGlobalShowCancelled(ShowCancelled mode) {
  has_global_showcancelled_ = true;
  global_showcancelled_ = mode;
}

ShowCancelled SpecifyManager::ResolveShowCancelled(
    std::string_view output) const {
  // The invocation option, when present, overrides every specify block
  // declaration.
  if (has_global_showcancelled_) return global_showcancelled_;
  auto it = path_output_showcancelled_.find(std::string(output));
  if (it != path_output_showcancelled_.end()) return it->second;
  // Absent both, the default is noshowcancelled.
  return ShowCancelled::kNoshowcancelled;
}

void SpecifyManager::AddInterconnectDelay(InterconnectDelay delay) {
  if (delay.src_port.empty()) {
    interconnect_delays_.erase(
        std::remove_if(interconnect_delays_.begin(), interconnect_delays_.end(),
                       [&](const InterconnectDelay& existing) {
                         return existing.dst_port == delay.dst_port;
                       }),
        interconnect_delays_.end());
    interconnect_delays_.push_back(std::move(delay));
    return;
  }

  for (auto& existing : interconnect_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port) {
      existing = std::move(delay);
      return;
    }
  }
  interconnect_delays_.push_back(std::move(delay));
}

uint64_t SpecifyManager::GetPathDelay(std::string_view src,
                                      std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) {
      return pd.delays[0];
    }
  }
  return 0;
}

bool SpecifyManager::HasPathDelay(std::string_view src,
                                  std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) return true;
  }
  return false;
}

bool SpecifyManager::CheckSetupViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         std::string_view data,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetup) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kHold) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

bool SpecifyManager::CheckRemovalViolation(std::string_view ref,
                                           uint64_t ref_time,
                                           std::string_view data,
                                           uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRemoval) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckRecoveryViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRecovery) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

// Shared implementation for the two-sided timing checks (recrem / setuphold).
// Both checks share an identical structure: filter by kind/signals, handle the
// negative-timing-check window, then compare the elapsed time against a pair of
// limits. The only behavioral difference is which limit applies on each side of
// the reference time: recrem uses limit2 for the "before" side and limit for
// the "after" side, while setuphold uses the opposite. `lower_side_limit`
// selects which member is compared when data_time <= ref_time, and
// `upper_side_limit` when data_time > ref_time.
namespace {

// True when `data_time` falls inside the negative-timing-check window centered
// on `ref_time` and spanning [-signed_limit, +signed_limit2].
bool NegativeTimingWindowViolated(const TimingCheckEntry& check,
                                  uint64_t ref_time, uint64_t data_time) {
  const auto kRefT = static_cast<int64_t>(ref_time);
  const auto kDataT = static_cast<int64_t>(data_time);
  const int64_t kLower = kRefT - check.signed_limit;
  const int64_t kUpper = kRefT + check.signed_limit2;
  return kDataT > kLower && kDataT < kUpper;
}

// True when the elapsed time between `ref_time` and `data_time` violates the
// side-specific limit (lower side for data on/before ref, upper side after).
bool TwoSidedLimitViolated(const TimingCheckEntry& check, uint64_t ref_time,
                           uint64_t data_time,
                           uint64_t TimingCheckEntry::* lower_side_limit,
                           uint64_t TimingCheckEntry::* upper_side_limit) {
  if (check.limit == 0 && check.limit2 == 0) return false;
  if (data_time <= ref_time) {
    return ref_time - data_time < check.*lower_side_limit;
  }
  return data_time - ref_time < check.*upper_side_limit;
}

}  // namespace

bool CheckTimingViolation(const std::vector<TimingCheckEntry>& timing_checks,
                          TimingCheckKind kind, const TimingCheckEvent& event,
                          const TwoSidedLimitSelector& selector) {
  for (const auto& check : timing_checks) {
    if (check.kind != kind) continue;
    if (check.ref_signal != event.ref) continue;
    if (check.data_signal != event.data) continue;
    if (check.negative_timing_check_enabled) {
      if (NegativeTimingWindowViolated(check, event.ref_time, event.data_time))
        return true;
      continue;
    }
    if (TwoSidedLimitViolated(check, event.ref_time, event.data_time,
                              selector.lower, selector.upper)) {
      return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  // §31.9.4: the option that switches all timing checks off suppresses this
  // check the same way it suppresses $setuphold.
  if (timing_check_options_.all_timing_checks_off) return false;
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kRecrem,
      {ref, ref_time, data, data_time},
      {&TimingCheckEntry::limit2, &TimingCheckEntry::limit});
}

bool SpecifyManager::CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSkew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckTimeskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kTimeskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

namespace {

bool FullskewWindowViolated(const TimingCheckEntry& check, uint64_t ref_time,
                            uint64_t data_time) {
  if (ref_time < data_time) {
    return data_time - ref_time > check.limit;
  }
  if (data_time < ref_time) {
    return ref_time - data_time > check.limit2;
  }
  return false;
}

}  // namespace

bool SpecifyManager::CheckFullskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kFullskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (FullskewWindowViolated(check, ref_time, data_time)) return true;
  }
  return false;
}

bool SpecifyManager::CheckWidthViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kWidth) continue;
    if (check.ref_signal != ref) continue;

    if (data_time <= ref_time) continue;
    uint64_t elapsed = data_time - ref_time;

    if (elapsed > check.threshold && elapsed < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckNochangeViolation(std::string_view ref,
                                            uint64_t leading_ref_time,
                                            uint64_t trailing_ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kNochange) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    int64_t begin =
        static_cast<int64_t>(leading_ref_time) - check.start_edge_offset;
    int64_t end =
        static_cast<int64_t>(trailing_ref_time) + check.end_edge_offset;
    auto t = static_cast<int64_t>(data_time);

    if (begin < t && t < end) return true;
  }
  return false;
}

bool SpecifyManager::CheckPeriodViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kPeriod) continue;
    if (check.ref_signal != ref) continue;

    if (data_time <= ref_time) continue;

    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= timestamp_time) return false;
  uint64_t elapsed = next_event_time - timestamp_time;
  if (event_based_flag) {
    return next_event_is_timecheck && elapsed > limit;
  }

  return elapsed > limit;
}

FullskewWindowAction FullskewSecondTimestampAction(
    bool timestamp_condition_holds, bool remain_active_flag) {
  // A timestamp whose condition holds (or that carries no condition) always
  // opens a fresh timing window, superseding any window in progress and
  // re-arming the check if it was dormant.
  if (timestamp_condition_holds) return FullskewWindowAction::kReplaceWindow;

  // With a false condition the remain_active_flag is decisive: when set, the
  // event is discarded and the existing window stands; when clear, the check
  // turns dormant.
  if (remain_active_flag) return FullskewWindowAction::kIgnore;
  return FullskewWindowAction::kGoDormant;
}

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= ref_time) return false;
  uint64_t elapsed = next_event_time - ref_time;
  if (event_based_flag) {
    return next_event_is_data && elapsed > limit;
  }

  return elapsed > limit;
}

Logic4Word ToggleNotifierOnViolation(Logic4Word current) {
  const bool kPreA = (current.aval & 1u) != 0u;
  const bool kPreB = (current.bval & 1u) != 0u;
  Logic4Word result;
  if (kPreA && kPreB) {
    result.aval = 1u;
    result.bval = 1u;
  } else if (kPreB || kPreA) {
    result.aval = 0u;
    result.bval = 0u;
  } else {
    result.aval = 1u;
    result.bval = 0u;
  }
  return result;
}

bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind) {
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
    case TimingCheckConditionKind::kNegate:
    case TimingCheckConditionKind::kCaseEq:
    case TimingCheckConditionKind::kCaseNeq:
      return true;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kNeq:
      return false;
  }
  return false;
}

bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit) {
  const bool kNown = (conditioning_lsb.bval & 1u) == 0u;
  if (!kNown) {
    return !IsDeterministicTimingCheckCondition(kind);
  }
  const auto kBit = static_cast<uint8_t>(conditioning_lsb.aval & 1u);
  const auto kRhs = static_cast<uint8_t>(scalar_constant_bit & 1u);
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
      return kBit == 1u;
    case TimingCheckConditionKind::kNegate:
      return kBit == 0u;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kCaseEq:
      return kBit == kRhs;
    case TimingCheckConditionKind::kNeq:
    case TimingCheckConditionKind::kCaseNeq:
      return kBit != kRhs;
  }
  return false;
}

TimingCheckConditionClass ClassifyTimingCheckCondition(const Expr* condition) {
  TimingCheckConditionClass result;
  if (condition == nullptr) return result;  // unconditioned event -> plain

  // `~ expression`: the bitwise-negation form of scalar_timing_check_condition.
  if (condition->kind == ExprKind::kUnary &&
      condition->op == TokenKind::kTilde) {
    result.kind = TimingCheckConditionKind::kNegate;
    return result;
  }

  // `expression <op> scalar_constant`: the four comparison forms. The LSB of
  // the right-hand scalar_constant is the value compared against.
  if (condition->kind == ExprKind::kBinary) {
    bool matched = true;
    switch (condition->op) {
      case TokenKind::kEqEq:
        result.kind = TimingCheckConditionKind::kEq;
        break;
      case TokenKind::kEqEqEq:
        result.kind = TimingCheckConditionKind::kCaseEq;
        break;
      case TokenKind::kBangEq:
        result.kind = TimingCheckConditionKind::kNeq;
        break;
      case TokenKind::kBangEqEq:
        result.kind = TimingCheckConditionKind::kCaseNeq;
        break;
      default:
        matched = false;
        break;
    }
    if (matched) {
      if (condition->rhs != nullptr) {
        result.scalar_constant_bit =
            static_cast<uint8_t>(condition->rhs->int_val & 1u);
      }
      return result;
    }
  }

  // Any other expression is the plain form: its own value gates the check.
  return result;
}

bool IsSingleSignalTimingCheck(TimingCheckKind kind) {
  return kind == TimingCheckKind::kWidth || kind == TimingCheckKind::kPeriod;
}

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode) {
  if (mode == TimingCheckVectorMode::kSingle) return 1u;

  if (IsSingleSignalTimingCheck(kind)) {
    return static_cast<uint64_t>(ref_width);
  }
  return static_cast<uint64_t>(ref_width) * static_cast<uint64_t>(data_width);
}

uint32_t VectorTransitionViolationCount(uint64_t before, uint64_t after,
                                        uint32_t width) {
  if (width == 0) return 0u;
  // Mask off any bits beyond the vector width, then count the positions whose
  // value differs -- each is one single-bit transition, hence one violation.
  uint64_t mask = (width >= 64u) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1u);
  uint64_t changed = (before ^ after) & mask;
  uint32_t count = 0;
  while (changed != 0) {
    changed &= (changed - 1u);
    ++count;
  }
  return count;
}

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
    case TimingCheckKind::kNochange:
      return true;

    case TimingCheckKind::kSkew:
    case TimingCheckKind::kFullskew:
    case TimingCheckKind::kTimeskew:
      return false;
  }
  return false;
}

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit) {
  if (adjusted_limit <= 0) {
    return {0u, true};
  }
  return {static_cast<uint64_t>(adjusted_limit), false};
}

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks) {
  if (upper <= lower) return false;

  const int64_t kMinWidth = 2 * static_cast<int64_t>(precision_ticks);
  return (upper - lower) >= kMinWidth;
}

uint64_t LatchedNegativeTimingWindowValue(int64_t window_lower,
                                          int64_t window_upper,
                                          int64_t data_transition_time,
                                          uint64_t old_value,
                                          uint64_t new_value) {
  (void)window_upper;
  // The new value is stable across the excluded-endpoint interior only when the
  // data has already settled by the time the window opens; a change at or after
  // the open boundary leaves the old value as the stable (and, inside the
  // window, incorrectly clocked) one.
  return data_transition_time <= window_lower ? new_value : old_value;
}

bool ImplicitDelayedSignalsRequired(bool negative_setup_or_hold_present,
                                    bool explicit_delayed_signals_declared) {
  return negative_setup_or_hold_present && !explicit_delayed_signals_declared;
}

uint64_t EffectiveOutputDelayWithTimingCheckSignalDelay(
    uint64_t propagation_delay, uint64_t timing_check_signal_delay) {
  return timing_check_signal_delay > propagation_delay
             ? timing_check_signal_delay
             : propagation_delay;
}

std::vector<ResolvedDelayedSignal> ResolveDelayedSignals(
    const std::vector<std::pair<std::string, std::string>>& refs) {
  std::vector<ResolvedDelayedSignal> resolved;
  for (const auto& [signal, delayed_name] : refs) {
    ResolvedDelayedSignal* existing = nullptr;
    for (auto& entry : resolved) {
      if (entry.signal == signal) {
        existing = &entry;
        break;
      }
    }
    if (existing == nullptr) {
      // First time this signal is seen: one copy, explicit if declared here.
      resolved.push_back({signal, delayed_name, !delayed_name.empty()});
      continue;
    }
    // The signal already has its single shared copy. If this check supplies an
    // explicit name and the copy is still implicit, promote it -- an explicit
    // declaration in any referencing check is used for all of them.
    if (!existing->is_explicit && !delayed_name.empty()) {
      existing->delayed_name = delayed_name;
      existing->is_explicit = true;
    }
  }
  return resolved;
}

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits) {
  size_t best_index = limits.size();
  for (size_t i = 0; i < limits.size(); ++i) {
    if (limits[i] >= 0) continue;
    if (best_index == limits.size() || limits[i] > limits[best_index]) {
      best_index = i;
    }
  }
  if (best_index == limits.size()) return false;
  limits[best_index] = 0;
  return true;
}

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }

  if (signed_setup < 0) return NegativeTimingConditionRole::kRef;

  if (signed_hold < 0) return NegativeTimingConditionRole::kData;

  return NegativeTimingConditionRole::kBoth;
}

}  // namespace delta
