// §30.7 and §32: what a module path's pulse limits and pulse styles are, and
// what changes them after elaboration. SpecifyManager::AddSdfPulseLimit and
// SpecifyManager::IncrementSdfPulseLimit place §32.7's SDF pulse limits on the
// paths of one named instance; SpecifyManager::ResolvePulseControlSpecparams
// and SpecifyManager::ApplyPathSpecificPulseControl apply §30.7.1's PATHPULSE$
// specparams in the precedence that subclause states;
// SpecifyManager::ResolvePulseStyle and SpecifyManager::ResolveShowCancelled
// answer §30.7.4's pulsestyle and showcancelled declarations against the
// invocation options that override them; and
// SpecifyManager::SetSpecparamValue, SpecifyManager::IncrementSpecparamValue
// and the Rebuild*ForSpecparam members recompute the path delays, timing
// checks and gate delays whose expressions read a specparam §32.4.3 annotated
// a new value onto. SpecifyManager::AddInterconnectDelay,
// SpecifyManager::GetPathDelay and SpecifyManager::HasPathDelay stand here as
// well, writing and reading the interconnect_delays_ and path_delays_ the
// limits above are placed on.
//
// §31's violation checks -- SpecifyManager::CheckSetupViolation and the other
// Check*Violation members -- stand in
// src/simulator/specify_timing_violation.cpp.

#include <algorithm>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
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
    std::string_view inst_prefix, const std::vector<std::string>& changed) {
  for (const auto& registered : path_decls_) {
    // A specparam of one instance is not the one an identically spelled
    // declaration in another reads, so only that instance's paths are rebuilt.
    if (registered.inst_prefix != inst_prefix) continue;
    if (!AnyExprReadsSpecparam(registered.decl->delays, changed)) continue;
    // The delay reads the specparam by its bare name, and it must read the one
    // belonging to the instance that declared the path. SimContext resolves a
    // bare name against the running process's instance, which during a run is
    // whichever process called $sdf_annotate.
    InstancePrefixOverride scope(specparam_ctx_->InstancePrefixOverride(),
                                 registered.inst_prefix);
    PathDelay pd = BuildPathDelayFromDecl(*registered.decl, *specparam_ctx_,
                                          *specparam_arena_);
    // The rebuilt path is filed back at the instance the declaration was
    // registered under (§30.4): AddPathDelay compares PathDelay::inst_prefix,
    // so a rebuild at the empty prefix lands beside the declared path.
    pd.inst_prefix = registered.inst_prefix;
    AddPathDelay(std::move(pd), /*preserve_pulse_limits=*/true);
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
//
// The instance is compared alongside the output port. §29.8 puts a primitive
// instance inside a module and §28.4 names its terminals by the declaring
// module's own port names, so two instances of one cell drive outputs spelled
// identically and the port alone would overwrite whichever instance's driver
// stands first.
void SpecifyManager::ReplacePrimitiveDriver(PrimitiveDriver rebuilt) {
  for (auto& existing : primitive_drivers_) {
    if (existing.output_port == rebuilt.output_port &&
        existing.inst_prefix == rebuilt.inst_prefix) {
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
    std::string_view inst_prefix, const std::vector<std::string>& changed) {
  for (const auto& registered : gate_decls_) {
    // §29.8 puts a primitive instance inside a module, and a specparam of one
    // instance is not the one an identically spelled declaration in another
    // reads, so only that instance's gates are rebuilt.
    if (registered.inst_prefix != inst_prefix) continue;
    const ModuleItem* gate = registered.gate;
    const Expr* const kDelays[3] = {gate->gate_delay, gate->gate_delay_fall,
                                    gate->gate_delay_decay};
    if (!AnyExprReadsSpecparam(kDelays, changed)) continue;
    // A gate delay written as a specparam is read by its bare name, and it must
    // read the one belonging to the instance that declared the gate.
    // SimContext resolves a bare name against the running process's instance,
    // which during a run is whichever process called $sdf_annotate.
    InstancePrefixOverride scope(specparam_ctx_->InstancePrefixOverride(),
                                 registered.inst_prefix);
    for (auto& rebuilt : BuildPrimitiveDriversFromGate(*gate, *specparam_ctx_,
                                                       *specparam_arena_)) {
      // The rebuilt driver is filed back at the instance the declaration was
      // registered under (§28.4): ReplacePrimitiveDriver compares
      // PrimitiveDriver::inst_prefix, so a rebuild at the empty prefix
      // overwrites another instance's driver.
      rebuilt.inst_prefix = registered.inst_prefix;
      ReplacePrimitiveDriver(std::move(rebuilt));
    }
  }
}

void SpecifyManager::ApplyAnnotatedSpecparam(std::string_view inst_prefix,
                                             const std::string& name,
                                             uint64_t value) {
  if (specparam_ctx_ == nullptr) return;
  // §32.4.3: a LABEL section annotates to specparams. A name the instance did
  // not declare as a specparam therefore has nothing here for the annotation to
  // land on, whatever else the design may happen to call by that name.
  if (!IsDeclaredSpecparam(inst_prefix, name)) return;

  // Lowerer::CreateChildModuleVariables keys an instantiated module's specparam
  // under its instance prefix, and SimContext::FindVariable reads a dotted name
  // out of its own table, so the qualified name is what reaches the storage.
  std::string qualified = std::string(inst_prefix) + name;
  if (Variable* storage = specparam_ctx_->FindVariable(qualified);
      storage != nullptr) {
    const uint32_t kWidth =
        storage->value.width == 0 ? 32u : storage->value.width;
    storage->value = MakeLogic4VecVal(*specparam_arena_, kWidth, value);
  }

  // §32.4.3: an expression containing one or more specparams is reevaluated
  // when a value is annotated to it from an SDF file.
  const std::vector<std::string> kChanged{name};
  RebuildPathDelaysForSpecparam(inst_prefix, kChanged);
  RebuildTimingChecksForSpecparam(kChanged);
  RebuildGateDriversForSpecparam(inst_prefix, kChanged);
}

void SpecifyManager::SetSpecparamValue(SpecparamValue spec,
                                       std::string_view inst_prefix) {
  std::string name = spec.name;
  uint64_t value = spec.value;
  // Keyed per instance because §30.3 has a specify block declare its specparams
  // by bare names: what one instance's CELL record asked for is not another's.
  std::string key = std::string(inst_prefix) + spec.name;
  auto it = specparam_index_.find(key);
  if (it != specparam_index_.end()) {
    specparam_values_[it->second] = std::move(spec);
  } else {
    specparam_index_[key] = specparam_values_.size();
    specparam_values_.push_back(std::move(spec));
  }

  ApplyAnnotatedSpecparam(inst_prefix, name, value);

  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(value);
  }
}

void SpecifyManager::IncrementSpecparamValue(SpecparamValue delta,
                                             std::string_view inst_prefix) {
  std::string name = std::move(delta.name);
  uint64_t added = delta.value;
  uint64_t new_value = added;
  // Keyed per instance as in SetSpecparamValue, and the reason bites here: an
  // INCREMENT entry would otherwise add onto another instance's running total.
  std::string key = std::string(inst_prefix) + name;
  auto it = specparam_index_.find(key);
  if (it != specparam_index_.end()) {
    new_value = specparam_values_[it->second].value + added;
    specparam_values_[it->second].value = new_value;
  } else {
    specparam_index_[key] = specparam_values_.size();
    SpecparamValue stored;
    stored.name = name;
    stored.value = added;
    specparam_values_.push_back(std::move(stored));
  }
  ApplyAnnotatedSpecparam(inst_prefix, name, new_value);
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

// §30.3 puts a specify block inside a module declaration, so two instances of
// one cell hold paths spelled identically and PathDelay::inst_prefix is what
// tells them apart. `inst_prefix` is what SdfCellInstancePrefix
// (simulator/sdf_annotate.cpp) made of the entry's CELLINSTANCE below the §32.9
// module_instance operand, so the limits reach the paths of that one instance
// and of no other in-scope instance of the cell.
void SpecifyManager::AddSdfPulseLimit(const SdfPulseLimitSpec& spec,
                                      std::string_view inst_prefix) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != spec.src || pd.dst_port != spec.dst) continue;
    if (pd.inst_prefix != inst_prefix) continue;
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
  //
  // §30.7.1 says such a specparam applies "to all module paths defined in a
  // module", and a module here is one instance of it: §30.3 puts the specify
  // block inside the module declaration, so each instance declares its own
  // paths. Matching PathDelay::inst_prefix is what keeps a PATHPULSE$ declared
  // in one instance of a cell off the paths of another instance of it.
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

// §30.7.1: a path-specific PATHPULSE$in$out overrides only the path it names. A
// specparam that names no existing path (e.g. a non-first terminal of a
// multiple-path declaration) matches nothing and is thereby ignored. The path
// it names is a path of the instance whose specify block declared it, since
// §30.4 has a path name its terminals by the module's own port names and two
// instances of one cell therefore declare paths spelled identically, so
// PathDelay::inst_prefix is matched as well.
void SpecifyManager::ApplyPathSpecificPulseControl(
    const PulseControlSpecparam& s) {
  for (auto& pd : path_delays_) {
    if (s.input == std::string_view(pd.src_port) &&
        s.output == std::string_view(pd.dst_port) &&
        s.inst_prefix == std::string_view(pd.inst_prefix)) {
      ApplyPulseControlOverride(pd, s.reject, s.has_error, s.error);
    }
  }
}

// As with AddSdfPulseLimit above, `inst_prefix` is the prefix of the instance
// the SDF cell named, so the amounts reach the paths of that one instance
// rather than of every in-scope instance of the cell.
void SpecifyManager::IncrementSdfPulseLimit(std::string_view src,
                                            std::string_view dst,
                                            int64_t reject_delta,
                                            int64_t error_delta,
                                            std::string_view inst_prefix) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    if (pd.inst_prefix != inst_prefix) continue;
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

// The first path between the two ports, whichever instance declared it. §30.3
// puts a specify block inside a module declaration, so two instances of one
// cell hold paths spelled identically and this cannot tell them apart. A caller
// that needs the delay of one named instance reads GetPathDelays() and compares
// PathDelay::inst_prefix itself.
uint64_t SpecifyManager::GetPathDelay(std::string_view src,
                                      std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) {
      return pd.delays[0];
    }
  }
  return 0;
}

// Whether any instance declares a path between the two ports. As with
// GetPathDelay above, PathDelay::inst_prefix is not compared, so this cannot
// say which instance holds the path; a caller needing that reads
// GetPathDelays() and compares the prefix itself.
bool SpecifyManager::HasPathDelay(std::string_view src,
                                  std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) return true;
  }
  return false;
}

}  // namespace delta
