#include "simulator/specify.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <utility>

namespace delta {

// =============================================================================
// §30.5.1 path-delay helpers
// =============================================================================

uint64_t ClampPathDelay(int64_t signed_value) {
  return signed_value < 0 ? 0u : static_cast<uint64_t>(signed_value);
}

void ExpandTransitionDelays(PathDelay& pd) {
  // §30.5.1 / Table 30-2 — populate non-x transition slots:
  //   [0]=0->1, [1]=1->0, [2]=0->z, [3]=z->1, [4]=1->z, [5]=z->0.
  switch (pd.delay_count) {
    case 1: {
      // Count 1: every basic transition uses the single value.
      const uint64_t t = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = t;
      break;
    }
    case 2: {
      // Count 2: trise covers 0->1/0->z/z->1; tfall covers 1->0/1->z/z->0.
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      pd.delays[2] = trise;
      pd.delays[3] = trise;
      pd.delays[4] = tfall;
      pd.delays[5] = tfall;
      break;
    }
    case 3: {
      // Count 3: z-bound transitions share tz; trise/tfall keep their slots.
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      const uint64_t tz = pd.delays[2];
      pd.delays[3] = trise;
      pd.delays[4] = tz;
      pd.delays[5] = tfall;
      break;
    }
    default:
      // Counts 6 and 12 arrive already laid out as Table 30-2 expects.
      break;
  }

  // §30.5.2 / Table 30-3 — derive x-transition slots from the non-x slots
  // using the pessimistic min/max rules. Skip when all twelve delays were
  // specified explicitly: in that case slots [6..11] are already authoritative.
  if (pd.delay_count == 12) return;
  pd.delays[6]  = std::min(pd.delays[2], pd.delays[0]);  // 0->x
  pd.delays[7]  = std::max(pd.delays[3], pd.delays[0]);  // x->1
  pd.delays[8]  = std::min(pd.delays[4], pd.delays[1]);  // 1->x
  pd.delays[9]  = std::max(pd.delays[5], pd.delays[1]);  // x->0
  pd.delays[10] = std::max(pd.delays[4], pd.delays[2]);  // x->z
  pd.delays[11] = std::min(pd.delays[3], pd.delays[5]);  // z->x
}

// =============================================================================
// §30.5.3 delay selection
// =============================================================================

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot) {
  if (candidates.empty()) return 0;
  // "Most recently" is a single timestamp across every candidate — condition
  // truth does not enter until the filter below, so an earlier-but-true path
  // stays inactive when a later input transitioned, regardless of its guard.
  uint64_t max_time = 0;
  for (const auto& c : candidates) {
    if (c.last_transition_time > max_time) max_time = c.last_transition_time;
  }
  bool have_active = false;
  uint64_t best = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr) continue;
    if (c.last_transition_time != max_time) continue;
    if (!c.condition_true) continue;
    uint64_t d = c.path->delays[transition_slot];
    if (!have_active || d < best) {
      best = d;
      have_active = true;
    }
  }
  return have_active ? best : 0;
}

// =============================================================================
// §30.6 mixing module path delays and distributed delays
// =============================================================================

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum) {
  return std::max(module_path_delay, distributed_delay_sum);
}

// =============================================================================
// §30.7 pulse filtering
// =============================================================================

PulseClassification ClassifyPulse(uint64_t pulse_width, uint64_t reject_limit,
                                  uint64_t error_limit) {
  if (pulse_width >= error_limit) return PulseClassification::kPropagate;
  if (pulse_width >= reject_limit) return PulseClassification::kForceX;
  return PulseClassification::kReject;
}

void InitDefaultPulseLimits(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i];
    pd.error_limit[i] = pd.delays[i];
  }
}

// =============================================================================
// §30.7.1 PATHPULSE$ override
// =============================================================================

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error) {
  // A reject-only PATHPULSE$ collapses the X band to zero; mirror the reject
  // value into the error slot so ClassifyPulse can never observe has_error.
  const uint64_t effective_error = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = effective_error;
  }
}

// =============================================================================
// §30.7.2 global pulse-limit invocation options
// =============================================================================

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct) {
  // Silently raise an under-specified error percentage so the resulting X
  // band is well-formed regardless of how the CLI options were supplied.
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

// =============================================================================
// §30.7.3 SDF pulse-limit annotation
// =============================================================================

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error) {
  // Mirror reject to the error slot when SDF omitted the error limit, so the
  // X band is never undefined for downstream classification.
  const uint64_t effective_error = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = effective_error;
  }
}

// =============================================================================
// SpecifyManager
// =============================================================================

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  // §32.4.1: route by the SDF entry's conditional shape. A nonconditional
  // entry (empty condition and not ifnone) annotates "to all SystemVerilog
  // specify paths between those same two ports" — every existing PathDelay
  // sharing the source/destination pair receives the new delay payload
  // while keeping its own condition / ifnone identity, because the SV
  // declaration's conditional shape is independent of the SDF entry that
  // updated it. A conditional or ifnone SDF entry "shall annotate only to
  // SystemVerilog specify paths between those same two ports with the
  // same condition" — only the existing entry whose full identifying
  // tuple matches is replaced. In either case, when nothing matches the
  // new entry is appended so a fresh declaration can still take effect.
  //
  // §32.5 example 2: when the caller asked to preserve pulse limits,
  // each matched entry's existing reject_limit / error_limit are
  // snapshotted before the overwrite and restored afterwards, so an
  // extended-form IOPATH with empty pulse-limit parens can update the
  // delays without disturbing whatever a prior PATHPULSE or
  // PATHPULSEPERCENT installed.
  const bool sdf_is_nonconditional =
      delay.condition.empty() && !delay.is_ifnone;
  if (sdf_is_nonconditional) {
    bool matched = false;
    for (auto& existing : path_delays_) {
      if (existing.src_port == delay.src_port &&
          existing.dst_port == delay.dst_port) {
        // Preserve the SV declaration's own conditional identity — the
        // §32.4.1 rule updates payload, not the matched declaration's
        // condition.
        std::string saved_cond = existing.condition;
        bool saved_ifnone = existing.is_ifnone;
        uint64_t saved_reject[12];
        uint64_t saved_error[12];
        if (preserve_pulse_limits) {
          for (int i = 0; i < 12; ++i) {
            saved_reject[i] = existing.reject_limit[i];
            saved_error[i] = existing.error_limit[i];
          }
        }
        existing = delay;
        existing.condition = std::move(saved_cond);
        existing.is_ifnone = saved_ifnone;
        if (preserve_pulse_limits) {
          for (int i = 0; i < 12; ++i) {
            existing.reject_limit[i] = saved_reject[i];
            existing.error_limit[i] = saved_error[i];
          }
        }
        matched = true;
      }
    }
    if (!matched) path_delays_.push_back(std::move(delay));
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.condition == delay.condition &&
        existing.is_ifnone == delay.is_ifnone) {
      uint64_t saved_reject[12];
      uint64_t saved_error[12];
      if (preserve_pulse_limits) {
        for (int i = 0; i < 12; ++i) {
          saved_reject[i] = existing.reject_limit[i];
          saved_error[i] = existing.error_limit[i];
        }
      }
      existing = std::move(delay);
      if (preserve_pulse_limits) {
        for (int i = 0; i < 12; ++i) {
          existing.reject_limit[i] = saved_reject[i];
          existing.error_limit[i] = saved_error[i];
        }
      }
      return;
    }
  }
  path_delays_.push_back(std::move(delay));
}

void SpecifyManager::AddTimingCheck(TimingCheckEntry check) {
  // §32.4 + §32.4.1: replace any prior entry whose identifying tuple
  // matches the incoming check, so that successive backannotation passes
  // converge instead of accumulating duplicates. The tuple is (kind, both
  // signals, both edges, condition) — §32.4.1 names "the same type where
  // the names and conditions match" as the matcher, and the condition
  // text distinguishes two declarations that share kind+signals+edges but
  // differ only on the SystemVerilog `&&&` guard.
  for (auto& existing : timing_checks_) {
    if (existing.kind == check.kind &&
        existing.ref_signal == check.ref_signal &&
        existing.ref_edge == check.ref_edge &&
        existing.data_signal == check.data_signal &&
        existing.data_edge == check.data_edge &&
        existing.condition == check.condition) {
      existing = std::move(check);
      return;
    }
  }
  timing_checks_.push_back(std::move(check));
}

void SpecifyManager::AnnotateSdfTimingCheck(const SdfTcAnnotation& a) {
  // §32.4.2 paragraph 2: walk every stored TimingCheckEntry and apply
  // the per-property matching rule. The kind and the two signal names
  // are always required to agree — the table itself routes the
  // annotation by SystemVerilog kind, and a check's signals are part of
  // its identity. Each of `ref_edge`, `data_edge`, and `condition`
  // restricts the match only when the SDF check supplied a value;
  // `kNone` / empty leaves that property unrestricted, satisfying the
  // sentence-1 "regardless of whether conditions are present" rule.
  bool matched = false;
  for (auto& existing : timing_checks_) {
    if (existing.kind != a.kind) continue;
    if (existing.ref_signal != a.ref_signal) continue;
    if (existing.data_signal != a.data_signal) continue;
    if (a.ref_edge != SpecifyEdge::kNone &&
        existing.ref_edge != a.ref_edge) continue;
    if (a.data_edge != SpecifyEdge::kNone &&
        existing.data_edge != a.data_edge) continue;
    if (!a.condition.empty() && existing.condition != a.condition) continue;
    // Per-field write — Table 32-2's "x" cells leave their flag false so
    // the SystemVerilog entry's existing value survives the pass.
    if (a.set_limit) existing.limit = a.limit;
    if (a.set_limit2) existing.limit2 = a.limit2;
    if (a.set_start_edge_offset)
      existing.start_edge_offset = a.start_edge_offset;
    if (a.set_end_edge_offset) existing.end_edge_offset = a.end_edge_offset;
    matched = true;
  }
  if (matched) return;
  // No SystemVerilog match: append a fresh entry that mirrors the SDF's
  // identifying tuple so the annotation is still observable. Only the
  // fields the target asked to set are populated; the rest are left at
  // their zero-initialised defaults.
  TimingCheckEntry e;
  e.kind = a.kind;
  e.ref_signal = a.ref_signal;
  e.ref_edge = a.ref_edge;
  e.data_signal = a.data_signal;
  e.data_edge = a.data_edge;
  e.condition = a.condition;
  if (a.set_limit) e.limit = a.limit;
  if (a.set_limit2) e.limit2 = a.limit2;
  if (a.set_start_edge_offset) e.start_edge_offset = a.start_edge_offset;
  if (a.set_end_edge_offset) e.end_edge_offset = a.end_edge_offset;
  timing_checks_.push_back(std::move(e));
}

void SpecifyManager::AnnotateSdf(SdfAnnotation annotation) {
  sdf_annotations_.push_back(std::move(annotation));
}

void SpecifyManager::SetSpecparamValue(SpecparamValue spec) {
  // §32.4.3 sentence 2: capture the name and freshly installed value
  // before storing — `spec` is moved into the value table — so the
  // reevaluation fan-out below can refer to both. The store-then-fire
  // ordering is deliberate: callbacks may consult GetSpecparamValues()
  // for cross-references and must observe the new value already
  // committed.
  std::string name = spec.name;
  uint64_t value = spec.value;
  auto it = specparam_index_.find(spec.name);
  if (it != specparam_index_.end()) {
    specparam_values_[it->second] = std::move(spec);
  } else {
    specparam_index_[spec.name] = specparam_values_.size();
    specparam_values_.push_back(std::move(spec));
  }
  // §32.4.3 sentence 2: invoke every registered consumer of this
  // specparam name. The LRM names "any expression containing one or
  // more specparams" so all matching callbacks fire on every
  // annotation, not just the first.
  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(value);
  }
}

void SpecifyManager::RegisterSpecparamReevaluation(
    std::string name, std::function<void(uint64_t)> reevaluate) {
  // Append rather than replace so two expressions referencing the same
  // specparam each receive their own reevaluation cue.
  specparam_reevaluators_.emplace_back(std::move(name), std::move(reevaluate));
}

void SpecifyManager::AddSdfPulseLimit(std::string_view src,
                                       std::string_view dst, uint64_t reject,
                                       bool has_error, uint64_t error,
                                       bool is_percent) {
  // §32.4.1 Table 32-1 PATHPULSE / PATHPULSEPERCENT: walk every PathDelay
  // sharing the source/destination port pair. The table maps both rows to
  // pulse limits across all conditional and nonconditional siblings, so a
  // single SDF entry fans out across every such PathDelay regardless of
  // its condition / ifnone identity.
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    if (is_percent) {
      // The percent form scales each transition slot by reject/error
      // percentages, in the same shape as the §30.7.2 global option.
      // Silently raise an under-specified error percentage so the X band
      // is well-formed; a single-value SDF entry collapses the X band by
      // mirroring reject into error.
      uint64_t reject_pct = reject;
      uint64_t error_pct = has_error ? error : reject;
      if (error_pct < reject_pct) error_pct = reject_pct;
      for (int i = 0; i < 12; ++i) {
        pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
        pd.error_limit[i] = pd.delays[i] * error_pct / 100;
      }
    } else {
      ApplySdfPulseLimits(pd, reject, has_error, error);
    }
  }
}

void SpecifyManager::AddInterconnectDelay(InterconnectDelay delay) {
  // §32.5 example 5: "An INTERCONNECT annotation followed by a PORT
  // annotation shall cause the INTERCONNECT annotation to be
  // overwritten." A PORT (or NETDELAY) entry carries no source port —
  // its semantics are "the delay from all sources on the net to that
  // load" — so installing one must wipe every prior interconnect delay
  // landing on the same load, regardless of whether each prior was a
  // PORT baseline or a source-specific INTERCONNECT override. The §32.5
  // load-isolation companion still holds: only entries whose dst_port
  // matches the incoming load are removed, leaving unrelated loads
  // intact.
  if (delay.src_port.empty()) {
    interconnect_delays_.erase(
        std::remove_if(interconnect_delays_.begin(),
                       interconnect_delays_.end(),
                       [&](const InterconnectDelay& existing) {
                         return existing.dst_port == delay.dst_port;
                       }),
        interconnect_delays_.end());
    interconnect_delays_.push_back(std::move(delay));
    return;
  }
  // §32.4: an INTERCONNECT-shaped entry is identified by its source/
  // destination port pair, so a re-annotation under the same pair
  // replaces the prior rise/fall payload rather than appending a
  // parallel entry. §32.5 example 4 ("PORT followed by INTERCONNECT")
  // is satisfied here because a prior PORT baseline carries an empty
  // source and therefore does not collide with this branch's
  // (src, dst) tuple — the PORT entry is left in place beside the new
  // source-specific override.
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
  // Return the first matching declaration's primary slot. With §32.4.1
  // allowing multiple PathDelays per (src, dst) port pair (one per
  // condition variant), callers that need a specific conditional sibling
  // must iterate `GetPathDelays()` themselves; this helper preserves the
  // simple-case ergonomics that pre-§32.4.1 callers relied on.
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
    // §31.3.1: window is (ref_time - limit, ref_time); endpoints are not
    // part of the violation region, so both inequalities are strict.
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
    // §31.3.2: window is [ref_time, ref_time + limit); only the end is
    // excluded from the violation region, so the lower bound is inclusive
    // and the upper bound is strict.
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
    // §31.3.4: window is (ref_time - limit, ref_time); endpoints are not
    // part of the violation region, so both inequalities are strict.
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
    // §31.3.5: window is [ref_time, ref_time + limit); only the end is
    // excluded from the violation region, so the lower bound is inclusive
    // and the upper bound is strict.
    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRecrem) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    if (check.negative_timing_check_enabled) {
      // §31.9: $recrem shares the $setuphold signed-window formula —
      // the two checks must behave identically for negative values, so
      // this branch is a literal mirror of the $setuphold one with
      // `signed_limit` read as the recovery limit and `signed_limit2`
      // as the removal limit. See CheckSetupholdViolation for the
      // endpoint-strictness reasoning.
      const int64_t ref_t = static_cast<int64_t>(ref_time);
      const int64_t data_t = static_cast<int64_t>(data_time);
      const int64_t lower = ref_t - check.signed_limit;
      const int64_t upper = ref_t + check.signed_limit2;
      if (data_t > lower && data_t < upper) return true;
      continue;
    }
    // §31.3.6: both limits zero — $recrem shall never issue a violation.
    if (check.limit == 0 && check.limit2 == 0) continue;
    if (data_time <= ref_time) {
      // Data event first (or simultaneous with the reference): the reference
      // is the timecheck event and the active window is
      //   (ref_time - removal_limit, ref_time]
      // The end of the window is included, so simultaneous events with a
      // positive removal_limit fall inside the violation region.
      if (ref_time - data_time < check.limit2) return true;
    } else {
      // Data event second: the reference is the timestamp event and the
      // active window is [ref_time, ref_time + recovery_limit), with only the
      // end excluded.
      if (data_time - ref_time < check.limit) return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSkew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.4.1: a violation occurs when the data event follows the reference
    // event by strictly more than `limit`. The strict inequality also
    // implements the zero-limit carve-out: when `limit` is zero, simultaneous
    // transitions produce `0 > 0` (false) and therefore do not violate.
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
    // §31.4.2: a violation is reported only when
    //   (timecheck time) - (timestamp time) > limit
    // The strict inequality folds in both carve-outs the LRM names
    // explicitly: simultaneous transitions never violate (even at zero
    // limit), and a new timestamp event arriving exactly at the elapsed
    // limit boundary does not violate.
    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckFullskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kFullskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.4.3: the reference and data events can transition in either
    // order. When the reference transitions first it is the timestamp
    // event and the active window is bounded by limit 1; when the data
    // event transitions first the roles invert and limit 2 applies. The
    // strict inequality also encodes both carve-outs the LRM spells out:
    // simultaneous transitions never violate (even at zero limit), and a
    // new timestamp event arriving exactly at the elapsed boundary does
    // not violate.
    if (ref_time < data_time) {
      if (data_time - ref_time > check.limit) return true;
    } else if (data_time < ref_time) {
      if (ref_time - data_time > check.limit2) return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckWidthViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kWidth) continue;
    if (check.ref_signal != ref) continue;
    // §31.4.4: the data event is the opposite-edge transition on the
    // same reference signal, and the LRM states the two events shall
    // never occur at the same simulation time. Treat a non-greater
    // data_time as "no pulse closed yet" so callers need not pre-filter.
    if (data_time <= ref_time) continue;
    uint64_t elapsed = data_time - ref_time;
    // §31.4.4: violation predicate is the two-sided strict inequality
    //   threshold < elapsed < limit
    // The strict upper bound encodes "pulse width >= limit avoids a
    // violation"; the strict lower bound implements the glitch
    // carve-out that suppresses pulses at or below `threshold`.
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
    // §31.4.6 violation predicate:
    //   (leading_ref - start_edge_offset) < data_time
    //     < (trailing_ref + end_edge_offset)
    // Offsets are signed — a positive start_edge_offset extends the
    // window earlier, and a negative one shrinks the window's start
    // later; the end_edge_offset is symmetric about the trailing edge.
    // Compute in int64_t so that negative offsets applied to a small
    // reference-edge time do not underflow.
    int64_t begin = static_cast<int64_t>(leading_ref_time) -
                    check.start_edge_offset;
    int64_t end = static_cast<int64_t>(trailing_ref_time) +
                  check.end_edge_offset;
    int64_t t = static_cast<int64_t>(data_time);
    // Strict inequalities encode §31.4.6's "end points of the time
    // window are not included" rule. The same exclusion also
    // implements the example's simultaneous-edge carve-out: when both
    // offsets are zero, a data event at the leading or trailing
    // reference edge lands exactly on an endpoint and does not
    // violate.
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
    // §31.4.5: the data event is the same-edge transition on the same
    // reference signal, so it must follow the reference event. Treat a
    // non-greater data_time as "no period closed yet" so callers need
    // not pre-filter.
    if (data_time <= ref_time) continue;
    // §31.4.5 violation predicate:
    //   (timecheck time) - (timestamp time) < limit
    // The strict inequality encodes "elapsed >= limit avoids a
    // violation": a period at or above the limit is long enough.
    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

bool ReportsFullskewViolation(uint64_t timestamp_time,
                              uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag) {
  // §31.4.3: events at or before the timestamp do not open a window.
  // This subsumes the simultaneous-transition carve-out (no violation
  // when both events coincide, even at zero limit).
  if (next_event_time <= timestamp_time) return false;
  uint64_t elapsed = next_event_time - timestamp_time;
  if (event_based_flag) {
    // Event-based mode behaves like $skew for this window: only a
    // timecheck event past the limit witnesses a violation; a fresh
    // timestamp event silently begins a new window.
    return next_event_is_timecheck && elapsed > limit;
  }
  // Timer-based default: once the timer elapses any later event — a
  // timecheck or a fresh timestamp — witnesses a violation. Events
  // arriving exactly at the boundary do not violate, matching the
  // strict inequality and the explicit exact-expiration rule.
  return elapsed > limit;
}

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag) {
  // Bail out for events that aren't strictly later than the reference
  // event. This subsumes §31.4.2's simultaneous-transition rule (no
  // violation when both events coincide, even at zero limit) and ignores
  // out-of-order inputs.
  if (next_event_time <= ref_time) return false;
  uint64_t elapsed = next_event_time - ref_time;
  if (event_based_flag) {
    // Event-based mode: the check waits for a data event before
    // evaluating the predicate, mirroring $skew. A new reference event
    // simply re-arms the wait without producing a violation.
    return next_event_is_data && elapsed > limit;
  }
  // Timer-based default: the implicit timer fires at ref_time + limit.
  // Any observed event past that boundary witnesses a violation
  // (whether data or a fresh reference). Events arriving at exactly the
  // boundary do not violate, matching the strict inequality of the
  // §31.4.2 violation predicate and the explicit exact-expiration rule
  // for new timestamp events.
  return elapsed > limit;
}

// =============================================================================
// §31.6 notifier-update helper
// =============================================================================

Logic4Word ToggleNotifierOnViolation(Logic4Word current) {
  const bool pre_a = (current.aval & 1u) != 0u;
  const bool pre_b = (current.bval & 1u) != 0u;
  Logic4Word result;
  if (pre_a && pre_b) {
    // z pre-state: preserve the dual-rail z encoding (aval=1, bval=1).
    result.aval = 1u;
    result.bval = 1u;
  } else if (pre_b) {
    // x pre-state: resolve to 0 so that successive violations drive the
    // observable 0→1→0 toggle sequence.
    result.aval = 0u;
    result.bval = 0u;
  } else if (pre_a) {
    // 1 pre-state flips to 0.
    result.aval = 0u;
    result.bval = 0u;
  } else {
    // 0 pre-state flips to 1.
    result.aval = 1u;
    result.bval = 0u;
  }
  return result;
}

// =============================================================================
// §31.7 conditioned-event enablement helpers
// =============================================================================

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
  // Reduce the dual-rail encoding to the three cases §31.7 distinguishes:
  // known 0, known 1, or an unknown value. The LRM rule is phrased in
  // terms of the conditioning signal carrying an x, and the decision on x
  // is fixed by the operator's deterministic-vs-nondeterministic label —
  // regardless of what a literal four-valued evaluation of the operator
  // would produce.
  const bool known = (conditioning_lsb.bval & 1u) == 0u;
  if (!known) {
    return !IsDeterministicTimingCheckCondition(kind);
  }
  const uint8_t bit = static_cast<uint8_t>(conditioning_lsb.aval & 1u);
  const uint8_t rhs = static_cast<uint8_t>(scalar_constant_bit & 1u);
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
      return bit == 1u;
    case TimingCheckConditionKind::kNegate:
      return bit == 0u;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kCaseEq:
      return bit == rhs;
    case TimingCheckConditionKind::kNeq:
    case TimingCheckConditionKind::kCaseNeq:
      return bit != rhs;
  }
  return false;
}

// =============================================================================
// §31.8 vector-signal expansion helpers
// =============================================================================

bool IsSingleSignalTimingCheck(TimingCheckKind kind) {
  // The LRM names $period and $width as the single-signal checks: their
  // data event is the opposite-/same-edge transition on the same
  // reference signal, so the invocation only carries one signal even
  // though the underlying check still has two events.
  return kind == TimingCheckKind::kWidth ||
         kind == TimingCheckKind::kPeriod;
}

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode) {
  if (mode == TimingCheckVectorMode::kSingle) return 1u;
  // Per-bit expansion: a single-signal check has only the reference width
  // to fan out across, so the data-side argument is ignored. A two-signal
  // check fans out across the cross-product of the two widths.
  if (IsSingleSignalTimingCheck(kind)) {
    return static_cast<uint64_t>(ref_width);
  }
  return static_cast<uint64_t>(ref_width) * static_cast<uint64_t>(data_width);
}

// =============================================================================
// §31.9.1 negative-timing-check helpers
// =============================================================================

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind) {
  switch (kind) {
    // Window-based and single-signal kinds — limits are adjusted so the
    // notifier fires at the proper moment against the delayed signals.
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
    // Event-order kinds — delaying the inputs can reverse the observed
    // order of transitions, so the LRM forbids using the delayed copies
    // for these checks.
    case TimingCheckKind::kSkew:
    case TimingCheckKind::kFullskew:
    case TimingCheckKind::kTimeskew:
      return false;
  }
  return false;
}

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit) {
  // The LRM collapses "adjusted below zero" and "exactly zero" into one
  // case: both drop the limit to zero and require a warning. Only a
  // strictly positive input is accepted unchanged.
  if (adjusted_limit <= 0) {
    return {0u, true};
  }
  return {static_cast<uint64_t>(adjusted_limit), false};
}

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks) {
  // An empty or inverted interval has no interior, so no sample point
  // can ever lie strictly between the endpoints.
  if (upper <= lower) return false;
  // Rule (a): the interval must span at least two units of simulation
  // precision for any sample point to fall strictly inside the open
  // window. Scaling the two-unit floor by the caller's precision keeps
  // the rule correct regardless of the underlying tick size.
  const int64_t min_width = 2 * static_cast<int64_t>(precision_ticks);
  return (upper - lower) >= min_width;
}

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits) {
  // Track the index of the negative entry nearest to zero — the
  // conservative "least change" choice. Ties keep the earliest index
  // because the later entries compare as "strictly greater" against
  // the already-recorded value only when they actually are closer to
  // zero.
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

// =============================================================================
// §31.9.2 timestamp/timecheck condition role classification
// =============================================================================

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  // Both negative is mutually inconsistent per §31.9.1 — the resolver
  // must zero one side before the window direction is defined.
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }
  // Negative setup shifts the window past the reference edge, so the
  // reference is the first-to-transition delayed signal.
  if (signed_setup < 0) return NegativeTimingConditionRole::kRef;
  // Negative hold shifts the window before the reference edge, so data
  // is the first-to-transition delayed signal.
  if (signed_hold < 0) return NegativeTimingConditionRole::kData;
  // Non-negative on both sides: the equivalent $setup + $hold
  // decomposition exposes both sides to the timestamp condition.
  return NegativeTimingConditionRole::kBoth;
}

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  // Second-to-transition is the mirror image of TimestampConditionRole.
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }
  if (signed_setup < 0) return NegativeTimingConditionRole::kData;
  if (signed_hold < 0) return NegativeTimingConditionRole::kRef;
  return NegativeTimingConditionRole::kBoth;
}

// =============================================================================
// §31.9.3 notifier-toggle source rule
// =============================================================================

bool NegativeTimingCheckNotifierShouldToggle(
    bool delayed_adjusted_violation,
    bool /*undelayed_original_violation*/) {
  // The undelayed-signal / original-limit evaluation is accepted as
  // an argument so the two inputs named by the LRM are visible at
  // the call site, but the rule forbids it from driving the toggle —
  // consulting it here would reintroduce the exact behaviour §31.9.3
  // rules out. Only the delayed-signal / adjusted-limit evaluation
  // determines whether the notifier toggles.
  return delayed_adjusted_violation;
}

// =============================================================================
// §31.9.4 invocation-option gating
// =============================================================================

bool NegativeTimingCheckOptionActive(
    bool negative_timing_check_option_enabled,
    bool all_timing_checks_disabled) {
  // Two invocation options participate: one opts in to negative
  // values and the other turns off all timing checks. The LRM says
  // an all-checks-off run produces the same collapse as leaving
  // the negative option unset, so the disable flag wins over the
  // enable flag and the feature activates only when the first is
  // on while the second is off.
  return negative_timing_check_option_enabled && !all_timing_checks_disabled;
}

bool SpecifyManager::CheckSetupholdViolation(std::string_view ref,
                                             uint64_t ref_time,
                                             std::string_view data,
                                             uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetuphold) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    if (check.negative_timing_check_enabled) {
      // §31.9: evaluate the signed violation interval
      //   (ref_time - setup, ref_time + hold)
      // where `setup` is `signed_limit` and `hold` is `signed_limit2`.
      // Both endpoints are strict, so zero on either side collapses
      // the corresponding half to empty — in particular, both-zero
      // reproduces the §31.3.3 never-violate rule without a special
      // case. A negative setup leaves `lower > ref_time`, placing the
      // window entirely after the reference edge; a negative hold
      // leaves `upper < ref_time`, placing the window entirely before
      // it. The reference edge itself falls inside the interval only
      // when the window straddles it, which is exactly the baseline
      // positive-value shape.
      const int64_t ref_t = static_cast<int64_t>(ref_time);
      const int64_t data_t = static_cast<int64_t>(data_time);
      const int64_t lower = ref_t - check.signed_limit;
      const int64_t upper = ref_t + check.signed_limit2;
      if (data_t > lower && data_t < upper) return true;
      continue;
    }
    // §31.3.3: both limits zero — $setuphold shall never issue a violation.
    if (check.limit == 0 && check.limit2 == 0) continue;
    if (data_time <= ref_time) {
      // Data event first (or simultaneous with the reference): the reference
      // is the timecheck event and the active window is
      //   (ref_time - setup_limit, ref_time]
      // The end of the window is included, so simultaneous events with a
      // positive setup limit fall inside the violation region.
      if (ref_time - data_time < check.limit) return true;
    } else {
      // Data event second: the reference is the timestamp event and the
      // active window is [ref_time, ref_time + hold_limit), with only the
      // end excluded.
      if (data_time - ref_time < check.limit2) return true;
    }
  }
  return false;
}

}  // namespace delta
