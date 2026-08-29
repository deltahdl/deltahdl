// §31: registering a timing check the design declared, under the invocation
// options that decide what it means. BuildTimingCheckUnderOptions evaluates a
// TimingCheckDecl's timing_check_limit expressions into the TimingCheckEntry
// the checks read, SpecifyManager::AddTimingCheckUnderOptions files that entry
// and keeps the declaration for §32.4.3's rebuild, and
// SpecifyManager::SetTimingCheckInvocationOptions with
// SpecifyManager::ApplyTimingCheckInvocationOptions settle §31.9.4's rule that
// negative limits are handled only while the enabling option is in force. The
// free functions above them answer §31.9's negative timing checks on their own
// terms: TimecheckConditionRole, OperandGetsImplicitDelayedCopy,
// NegativeTimingCheckNotifierShouldToggle and
// ResolveDelayedSignalsUnderOptions.
//
// SpecifyManager::CheckSetupholdViolation stands here beside the
// BuildTimingCheckUnderOptions that fills in the limits it compares; the other
// Check*Violation members stand in
// src/simulator/specify_timing_violation.cpp. §32.4.4's and §32.5's
// interconnect delays -- the InterconnectTopology, the AnnotateSdf* members
// that place an InterconnectDelay, and
// SpecifyManager::StartInterconnectPropagation with
// SpecifyManager::PollInterconnectSources -- stand in
// src/simulator/specify_interconnect.cpp, which was split out of this file.

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"

namespace delta {

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }
  if (signed_setup < 0) return NegativeTimingConditionRole::kData;
  if (signed_hold < 0) return NegativeTimingConditionRole::kRef;
  return NegativeTimingConditionRole::kBoth;
}

bool OperandGetsImplicitDelayedCopy(TimingCheckOperandKind kind) {
  return kind == TimingCheckOperandKind::kReference ||
         kind == TimingCheckOperandKind::kData;
}

// §31.9.3: the notifier follows the delayed-signal/adjusted-limit verdict. The
// undelayed-input/original-limit verdict is deliberately unused: detection is
// delayed along with the signals, so the toggle happens at the delayed moment.
bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool) {
  return delayed_adjusted_violation;
}

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled) {
  return negative_timing_check_option_enabled && !all_timing_checks_disabled;
}

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active) {
  if (!negative_timing_option_active) return 0;
  return requested_delay;
}

bool NegativeTimingCheckValuesAccepted(
    bool negative_value_present, const TimingCheckInvocationOptions& options) {
  return negative_value_present &&
         NegativeTimingCheckOptionActive(options.negative_timing_checks,
                                         options.all_timing_checks_off);
}

EffectiveDelayedSignals ResolveDelayedSignalsUnderOptions(
    const TimingCheckDecl& decl, int64_t requested_ref_delay,
    int64_t requested_data_delay, const TimingCheckInvocationOptions& options) {
  const bool kActive = NegativeTimingCheckOptionActive(
      options.negative_timing_checks, options.all_timing_checks_off);

  const std::string kRefOriginal(decl.ref_terminal.name);
  const std::string kDataOriginal(decl.data_terminal.name);

  EffectiveDelayedSignals out;
  out.are_copies_of_originals = !kActive;
  if (!kActive) {
    // The model may still declare delayed signals; run without the enabling
    // option they carry the original values, undelayed.
    out.ref_signal = kRefOriginal;
    out.data_signal = kDataOriginal;
    out.ref_delay = EffectiveTimingCheckSignalDelay(requested_ref_delay, false);
    out.data_delay =
        EffectiveTimingCheckSignalDelay(requested_data_delay, false);
    return out;
  }

  // Negative-value handling is in force: an explicitly declared delayed signal
  // names the copy the model can also use; otherwise the copy is the internal
  // (unnamed) one of §31.9.1, tracked here under the original signal's name.
  out.ref_signal =
      decl.delayed_ref.empty() ? kRefOriginal : std::string(decl.delayed_ref);
  out.data_signal = decl.delayed_data.empty() ? kDataOriginal
                                              : std::string(decl.delayed_data);
  out.ref_delay = EffectiveTimingCheckSignalDelay(requested_ref_delay, true);
  out.data_delay = EffectiveTimingCheckSignalDelay(requested_data_delay, true);
  return out;
}

namespace {

// Evaluates one timing_check_limit expression to a signed value. An absent
// expression is zero.
int64_t EvalTimingCheckLimit(Expr* limit, SimContext& ctx, Arena& arena) {
  if (limit == nullptr) return 0;
  Logic4Vec value = EvalExpr(limit, ctx, arena);
  const uint32_t kWidth = value.width == 0 ? 64u : value.width;
  return SignExtend(value.ToUint64(), kWidth);
}

// §31.5: the edge_descriptor list a run reads, from the one the parser
// collected. Syntax 31-15 writes z_or_x as any of `x`, `X`, `z` and `Z`, and
// the clause has "edge transitions involving z ... treated the same way as edge
// transitions involving x", so all four fold to 'x' here and the run has three
// levels to compare rather than five spellings. `0` and `1` are carried
// through as written.
std::vector<std::pair<char, char>> RunTimeEdgeDescriptors(
    const std::vector<std::pair<char, char>>& parsed) {
  auto fold = [](char c) { return c == '0' || c == '1' ? c : 'x'; };
  std::vector<std::pair<char, char>> folded;
  folded.reserve(parsed.size());
  for (const std::pair<char, char>& descriptor : parsed) {
    folded.emplace_back(fold(descriptor.first), fold(descriptor.second));
  }
  return folded;
}

// §31.9.4: the unsigned limit a check evaluates with once negative values are
// not being handled. Only the ordinary two-sided treatment is left, where a
// negative value has no meaning and counts as zero.
uint64_t UnhandledNegativeLimit(int64_t signed_limit) {
  return signed_limit < 0 ? 0u : static_cast<uint64_t>(signed_limit);
}

}  // namespace

TimingCheckEntry BuildTimingCheckUnderOptions(
    const TimingCheckDecl& decl, SimContext& ctx, Arena& arena,
    const TimingCheckInvocationOptions& options) {
  TimingCheckEntry entry;
  entry.kind = decl.check_kind;
  entry.ref_signal = std::string(decl.ref_terminal.name);
  entry.ref_edge = decl.ref_edge;
  entry.data_signal = std::string(decl.data_terminal.name);
  entry.data_edge = decl.data_edge;
  entry.notifier = std::string(decl.notifier);
  entry.loc = decl.loc;

  // §31.5: the edge_control_specifier each event was written with, in the two
  // forms the clause gives it. The SpecifyEdge above says which form was
  // written and answers posedge and negedge on its own; the list is what an
  // event written `edge[...]` is matched against, and it is empty for the
  // other events.
  entry.ref_edge_descriptors =
      RunTimeEdgeDescriptors(decl.ref_edge_descriptors);
  entry.data_edge_descriptors =
      RunTimeEdgeDescriptors(decl.data_edge_descriptors);

  // §32.4.1: backannotation looks for a timing check of the same type whose
  // names *and* conditions match, so a check declared with a conditioned event
  // (§31.7) carries that condition in comparable form. An SDF timing check
  // names its condition on the reference signal, so that one identifies the
  // check; a condition carried only by the data signal identifies it instead.
  entry.condition = SpecifyConditionText(decl.ref_condition);
  if (entry.condition.empty()) {
    entry.condition = SpecifyConditionText(decl.data_condition);
  }

  // §31.7: the same two conditions in the form the run can ask. The text above
  // renders one of them for SDF matching and drops the other, and neither text
  // answers whether the condition holds at the moment its event happens, which
  // is what decides whether the event enables the check at all.
  entry.ref_condition_expr = decl.ref_condition;
  entry.data_condition_expr = decl.data_condition;

  const int64_t kFirst = EvalTimingCheckLimit(
      decl.limits.empty() ? nullptr : decl.limits[0], ctx, arena);
  const int64_t kSecond = EvalTimingCheckLimit(
      decl.limits.size() < 2 ? nullptr : decl.limits[1], ctx, arena);

  entry.signed_limit = kFirst;
  entry.signed_limit2 = kSecond;

  // §31.9.4: whether the negative values the declaration carries are handled at
  // all is decided by the invocation option, not by the declaration.
  const bool kNegativePresent = kFirst < 0 || kSecond < 0;
  entry.negative_timing_check_enabled =
      NegativeTimingCheckValuesAccepted(kNegativePresent, options);

  entry.limit = UnhandledNegativeLimit(kFirst);
  entry.limit2 = UnhandledNegativeLimit(kSecond);
  return entry;
}

void SpecifyManager::SetTimingCheckInvocationOptions(
    TimingCheckInvocationOptions options) {
  timing_check_options_ = options;
  ApplyTimingCheckInvocationOptions();
}

void SpecifyManager::ApplyTimingCheckInvocationOptions() {
  if (NegativeTimingCheckOptionActive(
          timing_check_options_.negative_timing_checks,
          timing_check_options_.all_timing_checks_off)) {
    return;
  }
  // §31.9.4: negative values are handled only while the enabling option is in
  // force, however a check came to carry them -- a declaration built earlier,
  // or a limit that arrived by backannotation. Without that option in force
  // every registered check falls back to its ordinary two-sided treatment.
  for (auto& check : timing_checks_) {
    if (!check.negative_timing_check_enabled) continue;
    check.negative_timing_check_enabled = false;
    if (check.signed_limit < 0) {
      check.limit = UnhandledNegativeLimit(check.signed_limit);
    }
    if (check.signed_limit2 < 0) {
      check.limit2 = UnhandledNegativeLimit(check.signed_limit2);
    }
  }
}

void SpecifyManager::AddTimingCheckUnderOptions(const TimingCheckDecl& decl,
                                                SimContext& ctx, Arena& arena,
                                                std::string_view inst_prefix) {
  TimingCheckEntry entry =
      BuildTimingCheckUnderOptions(decl, ctx, arena, timing_check_options_);
  // §31.3 names a check's reference and data signals by the declaring module's
  // own port names, so the instance is what tells two instances of one cell
  // apart when AnnotateSdfTimingCheck looks for the check an SDF TIMINGCHECK
  // entry names.
  entry.inst_prefix = inst_prefix;
  AddTimingCheck(std::move(entry));
  // §32.4.3: a timing check limit is an expression too, so keep the declaration
  // in order to recompute it if an SDF LABEL changes a specparam it reads.
  //
  // §31.2 puts a system timing check inside a specify block and §30.3 puts that
  // block inside a module declaration, so one declaration is registered once
  // per instance of the cell holding it and the declaration alone does not
  // identify what was already kept. The instance travels with it because
  // RebuildTimingChecksForSpecparam evaluates the limit expressions in, and
  // files the rebuilt check back at, the instance the declaration came from.
  for (const auto& seen : timing_check_decls_) {
    if (seen.decl == &decl && seen.inst_prefix == inst_prefix) return;
  }
  timing_check_decls_.push_back({&decl, std::string(inst_prefix)});
}

bool SpecifyManager::CheckSetupholdViolation(std::string_view ref,
                                             uint64_t ref_time,
                                             std::string_view data,
                                             uint64_t data_time) const {
  // §31.9.4: with the invocation option that switches all timing checks off,
  // nothing is checked and so no violation is reported.
  if (timing_check_options_.all_timing_checks_off) return false;
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kSetuphold,
      {ref, ref_time, data, data_time},
      {&TimingCheckEntry::limit, &TimingCheckEntry::limit2});
}

}  // namespace delta
