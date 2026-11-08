#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

namespace delta {

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum) {
  return std::max(module_path_delay, distributed_delay_sum);
}

PulseClassification ClassifyPulse(uint64_t pulse_width, uint64_t reject_limit,
                                  uint64_t error_limit) {
  if (pulse_width >= error_limit) return PulseClassification::kPropagate;
  if (pulse_width >= reject_limit) return PulseClassification::kForceX;
  return PulseClassification::kReject;
}

uint64_t FilteredPulseLeadingXTime(PulseStyle style, uint64_t detect_time,
                                   uint64_t scheduled_leading_time) {
  return style == PulseStyle::kOnDetect ? detect_time : scheduled_leading_time;
}

bool IsNegativePulse(uint64_t leading_time, uint64_t trailing_time) {
  return trailing_time < leading_time;
}

NegativePulseSchedule ScheduleNegativePulse(ShowCancelled mode,
                                            PulseStyle style,
                                            uint64_t detect_time,
                                            uint64_t scheduled_leading_time) {
  if (mode == ShowCancelled::kNoshowcancelled) {
    return {false, 0};
  }
  return {true, FilteredPulseLeadingXTime(style, detect_time,
                                          scheduled_leading_time)};
}

void InitDefaultPulseLimits(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i];
    pd.error_limit[i] = pd.delays[i];
  }
  pd.reject_limit_source = PulseLimitSource::kDefault;
  pd.error_limit_source = PulseLimitSource::kDefault;
}

static bool PulseLimitSourceWins(PulseLimitSource standing,
                                 PulseLimitSource source) {
  return static_cast<uint8_t>(source) >= static_cast<uint8_t>(standing);
}

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error) {
  const uint64_t kEffectiveError = has_error ? error : reject;
  if (PulseLimitSourceWins(pd.reject_limit_source,
                           PulseLimitSource::kPathpulse)) {
    for (int i = 0; i < 12; ++i) pd.reject_limit[i] = reject;
    pd.reject_limit_source = PulseLimitSource::kPathpulse;
  }
  if (PulseLimitSourceWins(pd.error_limit_source,
                           PulseLimitSource::kPathpulse)) {
    for (int i = 0; i < 12; ++i) pd.error_limit[i] = kEffectiveError;
    pd.error_limit_source = PulseLimitSource::kPathpulse;
  }
}

void DerivePulseLimitsFromDelays(const uint64_t (&delays)[12],
                                 uint8_t reject_pct, uint8_t error_pct,
                                 uint64_t (&reject_limit)[12],
                                 uint64_t (&error_limit)[12]) {
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    reject_limit[i] = delays[i] * reject_pct / 100;
    error_limit[i] = delays[i] * error_pct / 100;
  }
}

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct) {
  uint64_t derived_reject[12];
  uint64_t derived_error[12];
  DerivePulseLimitsFromDelays(pd.delays, reject_pct, error_pct, derived_reject,
                              derived_error);
  if (PulseLimitSourceWins(pd.reject_limit_source, PulseLimitSource::kGlobal)) {
    for (int i = 0; i < 12; ++i) pd.reject_limit[i] = derived_reject[i];
    pd.reject_limit_source = PulseLimitSource::kGlobal;
  }
  if (PulseLimitSourceWins(pd.error_limit_source, PulseLimitSource::kGlobal)) {
    for (int i = 0; i < 12; ++i) pd.error_limit[i] = derived_error[i];
    pd.error_limit_source = PulseLimitSource::kGlobal;
  }
}

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error) {
  const uint64_t kEffectiveError = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = kEffectiveError;
  }
  pd.reject_limit_source = PulseLimitSource::kSdf;
  pd.error_limit_source = PulseLimitSource::kSdf;
}

template <typename Exprs>
static bool AnyExprReadsSpecparam(const Exprs& exprs,
                                  const std::vector<std::string>& changed) {
  for (const Expr* e : exprs) {
    if (ExprReadsSpecparam(e, changed)) return true;
  }
  return false;
}

void SpecifyManager::RebuildPathDelaysForSpecparam(
    std::string_view inst_prefix, const std::vector<std::string>& changed) {
  for (const auto& registered : path_decls_) {
    if (registered.inst_prefix != inst_prefix) continue;
    if (!AnyExprReadsSpecparam(registered.decl->delays, changed)) continue;
    InstancePrefixOverride scope(specparam_ctx_->InstancePrefixOverride(),
                                 registered.inst_prefix);
    PathDelay pd = BuildPathDelayFromDecl(
        *registered.decl, *specparam_ctx_, *specparam_arena_,
        registered.src_index, registered.dst_index);
    pd.inst_prefix = registered.inst_prefix;
    ReplacePathDelayRetaining(path_delays_[registered.path_index],
                              std::move(pd),
                              PathDelayRetention::PulseLimits(true, true));
  }
}

void SpecifyManager::RebuildTimingChecksForSpecparam(
    std::string_view inst_prefix, const std::vector<std::string>& changed) {
  for (const auto& registered : timing_check_decls_) {
    if (registered.inst_prefix != inst_prefix) continue;
    if (!AnyExprReadsSpecparam(registered.decl->limits, changed)) continue;
    InstancePrefixOverride scope(specparam_ctx_->InstancePrefixOverride(),
                                 registered.inst_prefix);
    TimingCheckEntry rebuilt =
        BuildTimingCheckUnderOptions(*registered.decl, *specparam_ctx_,
                                     *specparam_arena_, timing_check_options_);
    rebuilt.inst_prefix = registered.inst_prefix;
    AddTimingCheck(std::move(rebuilt));
  }
}

void SpecifyManager::ReplacePrimitiveDriver(PrimitiveDriver rebuilt) {
  for (auto& existing : primitive_drivers_) {
    if (existing.output_port == rebuilt.output_port &&
        existing.inst_prefix == rebuilt.inst_prefix) {
      rebuilt.drives_module_output = existing.drives_module_output;
      existing = std::move(rebuilt);
      return;
    }
  }
  primitive_drivers_.push_back(std::move(rebuilt));
}

void SpecifyManager::RebuildGateDriversForSpecparam(
    std::string_view inst_prefix, const std::vector<std::string>& changed) {
  for (const auto& registered : gate_decls_) {
    if (registered.inst_prefix != inst_prefix) continue;
    const ModuleItem* gate = registered.gate;
    const Expr* const kDelays[3] = {gate->gate_delay, gate->gate_delay_fall,
                                    gate->gate_delay_decay};
    if (!AnyExprReadsSpecparam(kDelays, changed)) continue;
    InstancePrefixOverride scope(specparam_ctx_->InstancePrefixOverride(),
                                 registered.inst_prefix);
    for (auto& rebuilt : BuildPrimitiveDriversFromGate(*gate, *specparam_ctx_,
                                                       *specparam_arena_)) {
      rebuilt.inst_prefix = registered.inst_prefix;
      ReplacePrimitiveDriver(std::move(rebuilt));
    }
  }
}

void SpecifyManager::ApplyAnnotatedSpecparam(std::string_view inst_prefix,
                                             const std::string& name,
                                             uint64_t value,
                                             double real_value) {
  if (specparam_ctx_ == nullptr) return;
  if (!IsDeclaredSpecparam(inst_prefix, name)) return;

  std::string qualified = std::string(inst_prefix) + name;
  if (Variable* storage = specparam_ctx_->FindVariable(qualified);
      storage != nullptr) {
    const uint32_t kWidth =
        storage->value.width == 0 ? 32u : storage->value.width;
    storage->value = storage->is_real
                         ? MakeRealVec(*specparam_arena_, real_value, kWidth)
                         : MakeLogic4VecVal(*specparam_arena_, kWidth, value);
  }

  const std::vector<std::string> kChanged =
      ReevaluateDependentSpecparams(inst_prefix, name);
  RebuildPathDelaysForSpecparam(inst_prefix, kChanged);
  RebuildTimingChecksForSpecparam(inst_prefix, kChanged);
  RebuildGateDriversForSpecparam(inst_prefix, kChanged);
}

namespace {

bool ReadsTheChangedSpecparam(
    const DeclaredSpecparam& declared, std::string_view inst_prefix,
    const std::vector<std::string>& changed,
    const std::vector<std::string>& reading,
    const std::unordered_map<std::string, std::size_t>& annotated) {
  if (declared.inst_prefix != inst_prefix || declared.init == nullptr) {
    return false;
  }
  if (std::ranges::find(changed, declared.name) != changed.end()) return false;
  if (annotated.contains(std::string(inst_prefix) + declared.name)) {
    return false;
  }
  return ExprReadsSpecparam(declared.init, reading);
}

void StoreSpecparamValue(Variable& storage, const Logic4Vec& value,
                         Arena& arena) {
  const double kReal = value.is_real ? RealVecToDouble(value)
                                     : static_cast<double>(value.ToUint64());
  if (storage.is_real) {
    storage.value = MakeRealVec(arena, kReal, storage.value.width);
    return;
  }
  storage.value = MakeLogic4VecVal(
      arena, storage.value.width,
      value.is_real ? static_cast<uint64_t>(std::llround(kReal))
                    : value.ToUint64());
}

}  // namespace

std::vector<std::string> SpecifyManager::ReevaluateDependentSpecparams(
    std::string_view inst_prefix, const std::string& annotated) {
  std::vector<std::string> changed{annotated};
  for (std::size_t next = 0; next < changed.size(); ++next) {
    const std::vector<std::string> kReading{changed[next]};
    for (const DeclaredSpecparam& declared : declared_specparams_) {
      if (!ReadsTheChangedSpecparam(declared, inst_prefix, changed, kReading,
                                    specparam_index_)) {
        continue;
      }
      Variable* storage = specparam_ctx_->FindVariable(
          std::string(inst_prefix) + declared.name);
      if (storage == nullptr) continue;
      InstancePrefixOverride scope(specparam_ctx_->InstancePrefixOverride(),
                                   inst_prefix);
      StoreSpecparamValue(
          *storage, EvalExpr(declared.init, *specparam_ctx_, *specparam_arena_),
          *specparam_arena_);
      changed.push_back(declared.name);
    }
  }
  return changed;
}

void SpecifyManager::SetSpecparamValue(SpecparamValue spec,
                                       std::string_view inst_prefix) {
  std::string name = spec.name;
  uint64_t value = spec.value;
  const double kRealValue = spec.real_value;
  std::string key = std::string(inst_prefix) + spec.name;
  auto it = specparam_index_.find(key);
  if (it != specparam_index_.end()) {
    specparam_values_[it->second] = std::move(spec);
  } else {
    specparam_index_[key] = specparam_values_.size();
    specparam_values_.push_back(std::move(spec));
  }

  ApplyAnnotatedSpecparam(inst_prefix, name, value, kRealValue);

  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(value);
  }
}

bool SpecifyManager::KnowsSpecparam(std::string_view inst_prefix,
                                    std::string_view name) const {
  if (IsDeclaredSpecparam(inst_prefix, name)) return true;
  return specparam_index_.contains(std::string(inst_prefix) +
                                   std::string(name));
}

double SpecifyManager::StoredSpecparamReal(std::string_view inst_prefix,
                                           const std::string& name) const {
  if (specparam_ctx_ == nullptr || !IsDeclaredSpecparam(inst_prefix, name))
    return 0.0;
  Variable* storage =
      specparam_ctx_->FindVariable(std::string(inst_prefix) + name);
  if (storage == nullptr) return 0.0;
  return storage->is_real ? RealVecToDouble(storage->value)
                          : static_cast<double>(storage->value.ToUint64());
}

uint64_t SpecifyManager::StoredSpecparamValue(std::string_view inst_prefix,
                                              const std::string& name) const {
  if (specparam_ctx_ == nullptr || !IsDeclaredSpecparam(inst_prefix, name))
    return 0;
  Variable* storage =
      specparam_ctx_->FindVariable(std::string(inst_prefix) + name);
  return storage != nullptr ? storage->value.ToUint64() : 0;
}

void SpecifyManager::IncrementSpecparamValue(SpecparamValue delta,
                                             std::string_view inst_prefix) {
  std::string name = std::move(delta.name);
  uint64_t added = delta.value;
  uint64_t new_value = added;
  double new_real = delta.real_value;
  std::string key = std::string(inst_prefix) + name;
  auto it = specparam_index_.find(key);
  if (it != specparam_index_.end()) {
    new_value = specparam_values_[it->second].value + added;
    new_real += specparam_values_[it->second].real_value;
    specparam_values_[it->second].value = new_value;
    specparam_values_[it->second].real_value = new_real;
  } else {
    new_value = StoredSpecparamValue(inst_prefix, name) + added;
    new_real += StoredSpecparamReal(inst_prefix, name);
    specparam_index_[key] = specparam_values_.size();
    SpecparamValue stored;
    stored.name = name;
    stored.value = new_value;
    stored.real_value = new_real;
    specparam_values_.push_back(std::move(stored));
  }
  ApplyAnnotatedSpecparam(inst_prefix, name, new_value, new_real);
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

uint64_t StatedPulseLimit(int64_t value) {
  return value < 0 ? 0U : static_cast<uint64_t>(value);
}

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

uint64_t AddPulseLimitDelta(uint64_t limit, int64_t delta) {
  const int64_t kMoved = static_cast<int64_t>(limit) + delta;
  return kMoved < 0 ? 0U : static_cast<uint64_t>(kMoved);
}

void IncrementPulseLimitsOnPath(PathDelay& pd, const SdfPulseLimitSpec& spec) {
  for (int i = 0; i < 12; ++i) {
    const SlotPulseLimitDeltas kDeltas =
        PulseLimitDeltasForSlot(spec, pd.delays[i]);
    pd.reject_limit[i] = AddPulseLimitDelta(pd.reject_limit[i], kDeltas.reject);
    pd.error_limit[i] = AddPulseLimitDelta(pd.error_limit[i], kDeltas.error);
  }
}

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
}

}  // namespace

bool SpecifyManager::AddSdfPulseLimit(const SdfPulseLimitSpec& spec,
                                      std::string_view inst_prefix) {
  bool placed = false;
  for (auto& pd : path_delays_) {
    if (pd.src_port != spec.src || pd.dst_port != spec.dst) continue;
    if (pd.inst_prefix != inst_prefix) continue;
    PlaceSdfPulseLimits(pd, spec);
    placed = true;
  }
  return placed;
}

void SpecifyManager::ResolvePulseControlSpecparams(
    const std::vector<PulseControlSpecparam>& specs) {
  for (const auto& s : specs) {
    if (!s.input.empty() || !s.output.empty()) continue;
    for (auto& pd : path_delays_) {
      if (s.inst_prefix != std::string_view(pd.inst_prefix)) continue;
      ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
    }
  }
  for (const auto& s : specs) {
    if (s.input.empty() && s.output.empty()) continue;
    ApplyPathSpecificPulseControl(s);
  }
}

void SpecifyManager::ApplyPathSpecificPulseControl(
    const PulseControlSpecparam& s) {
  for (auto& pd : path_delays_) {
    std::string_view input =
        pd.decl_src_port.empty() ? pd.src_port : pd.decl_src_port;
    std::string_view output =
        pd.decl_dst_port.empty() ? pd.dst_port : pd.decl_dst_port;
    if (s.input == input && s.output == output &&
        s.inst_prefix == std::string_view(pd.inst_prefix)) {
      ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
    }
  }
}

void SpecifyManager::IncrementSdfPulseLimit(
    std::string_view src, std::string_view dst,
    const SdfPulseLimitIncrement& deltas, std::string_view inst_prefix) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    if (pd.inst_prefix != inst_prefix) continue;
    for (std::size_t i = 0; i < 12; ++i) {
      const int64_t kNewReject =
          static_cast<int64_t>(pd.reject_limit[i]) + deltas.reject[i];
      const int64_t kNewError =
          static_cast<int64_t>(pd.error_limit[i]) + deltas.error[i];
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
  if (has_global_pulse_style_) return global_pulse_style_;
  auto it = path_output_pulse_styles_.find(std::string(output));
  if (it != path_output_pulse_styles_.end()) return it->second;
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
  if (has_global_showcancelled_) return global_showcancelled_;
  auto it = path_output_showcancelled_.find(std::string(output));
  if (it != path_output_showcancelled_.end()) return it->second;
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

}  // namespace delta
