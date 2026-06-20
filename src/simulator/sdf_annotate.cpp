#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <fstream>
#include <initializer_list>
#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

namespace delta {

static uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  switch (mtm) {
    case SdfMtm::kMinimum:
      return dv.min_val;
    case SdfMtm::kTypical:
      return dv.typ_val;
    case SdfMtm::kMaximum:
      return dv.max_val;
  }
  return dv.typ_val;
}

static void ExpandSdfDelaysTwo(std::vector<uint64_t>& out, uint64_t v1,
                               uint64_t v2) {
  out[0] = v1;
  out[1] = v2;
  out[2] = v1;
  out[3] = v1;
  out[4] = v2;
  out[5] = v2;
  out[6] = v1;
  out[7] = v1;
  out[8] = v2;
  out[9] = v2;
  out[10] = std::max(v1, v2);
  out[11] = std::min(v1, v2);
}

static void ExpandSdfDelaysThree(std::vector<uint64_t>& out, uint64_t v1,
                                 uint64_t v2, uint64_t v3) {
  out[0] = v1;
  out[1] = v2;
  out[2] = v3;
  out[3] = v1;
  out[4] = v3;
  out[5] = v2;
  out[6] = std::min(v1, v3);
  out[7] = std::max(v1, v3);
  out[8] = std::min(v2, v3);
  out[9] = v2;
  out[10] = v3;
  out[11] = std::min(v1, v2);
}

static void ExpandSdfDelaysSixDirect(std::vector<uint64_t>& out, uint64_t v1,
                                     uint64_t v2, uint64_t v3, uint64_t v4,
                                     uint64_t v5, uint64_t v6) {
  out[0] = v1;
  out[1] = v2;
  out[2] = v3;
  out[3] = v4;
  out[4] = v5;
  out[5] = v6;
}

static void ExpandSdfDelaysSixDerived(std::vector<uint64_t>& out, uint64_t v1,
                                      uint64_t v2, uint64_t v3, uint64_t v4,
                                      uint64_t v5, uint64_t v6) {
  out[6] = std::min(v1, v3);
  out[7] = std::max(v1, v4);
  out[8] = std::min(v2, v5);
  out[9] = std::max(v2, v6);
  out[10] = std::max(v3, v5);
  out[11] = std::min(v4, v6);
}

static void ExpandSdfDelaysSix(std::vector<uint64_t>& out, uint64_t v1,
                               uint64_t v2, uint64_t v3, uint64_t v4,
                               uint64_t v5, uint64_t v6) {
  ExpandSdfDelaysSixDirect(out, v1, v2, v3, v4, v5, v6);
  ExpandSdfDelaysSixDerived(out, v1, v2, v3, v4, v5, v6);
}

std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm) {
  std::vector<uint64_t> out(12, 0);
  if (vals.empty()) return out;

  const std::size_t kN = vals.size();
  const uint64_t kV1 = SelectMtm(vals[0], mtm);

  if (kN != 1 && kN != 2 && kN != 3 && kN != 6 && kN != 12) {
    std::fill(out.begin(), out.end(), kV1);
    return out;
  }

  if (kN == 1) {
    std::fill(out.begin(), out.end(), kV1);
    return out;
  }

  const uint64_t kV2 = SelectMtm(vals[1], mtm);
  if (kN == 2) {
    ExpandSdfDelaysTwo(out, kV1, kV2);
    return out;
  }

  const uint64_t kV3 = SelectMtm(vals[2], mtm);
  if (kN == 3) {
    ExpandSdfDelaysThree(out, kV1, kV2, kV3);
    return out;
  }

  const uint64_t kV4 = SelectMtm(vals[3], mtm);
  const uint64_t kV5 = SelectMtm(vals[4], mtm);
  const uint64_t kV6 = SelectMtm(vals[5], mtm);
  if (kN == 6) {
    ExpandSdfDelaysSix(out, kV1, kV2, kV3, kV4, kV5, kV6);
    return out;
  }

  for (std::size_t i = 0; i < 12; ++i) {
    out[i] = SelectMtm(vals[i], mtm);
  }
  return out;
}

std::array<uint64_t, 4> ReduceSdfDelaysToThree(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm) {
  std::array<uint64_t, 4> out{0, 0, 0, 0};
  if (vals.empty()) return out;

  out[0] = SelectMtm(vals[0], mtm);
  out[1] = vals.size() >= 2 ? SelectMtm(vals[1], mtm) : out[0];
  out[2] = vals.size() >= 3 ? SelectMtm(vals[2], mtm) : out[0];

  out[3] = std::min({out[0], out[1], out[2]});
  return out;
}

namespace {

// Mirrors the `push` lambda in ExpandSdfTimingCheckTargets: appends a new
// annotation seeded from the timing check and returns a reference to it.
SdfTcAnnotation& PushSdfTcAnnotation(std::vector<SdfTcAnnotation>& targets,
                                     const SdfTimingCheck& tc,
                                     TimingCheckKind kind) {
  SdfTcAnnotation a;
  a.kind = kind;
  a.ref_signal = tc.ref_port;
  a.ref_edge = tc.ref_edge;
  a.data_signal = tc.data_port;
  a.data_edge = tc.data_edge;
  a.condition = tc.condition;
  targets.push_back(std::move(a));
  return targets.back();
}

void PopulateSdfTcSetupHold(std::vector<SdfTcAnnotation>& targets,
                            const SdfTimingCheck& tc, SdfCheckType check_type,
                            uint64_t v1, uint64_t v2) {
  switch (check_type) {
    case SdfCheckType::kSetup: {
      auto& s = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetup);
      s.set_limit = true;
      s.limit = v1;
      auto& sh = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetuphold);
      sh.set_limit = true;
      sh.limit = v1;
      break;
    }
    case SdfCheckType::kHold: {
      auto& h = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kHold);
      h.set_limit = true;
      h.limit = v1;
      auto& sh = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetuphold);
      sh.set_limit2 = true;
      sh.limit2 = v1;
      break;
    }
    case SdfCheckType::kSetuphold: {
      auto& s = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetup);
      s.set_limit = true;
      s.limit = v1;
      auto& h = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kHold);
      h.set_limit = true;
      h.limit = v2;
      auto& sh = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetuphold);
      sh.set_limit = true;
      sh.limit = v1;
      sh.set_limit2 = true;
      sh.limit2 = v2;
      break;
    }
    default:
      break;
  }
}

void PopulateSdfTcRecRem(std::vector<SdfTcAnnotation>& targets,
                         const SdfTimingCheck& tc, SdfCheckType check_type,
                         uint64_t v1, uint64_t v2) {
  switch (check_type) {
    case SdfCheckType::kRecovery: {
      auto& r = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecovery);
      r.set_limit = true;
      r.limit = v1;
      auto& rr = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecrem);
      rr.set_limit = true;
      rr.limit = v1;
      break;
    }
    case SdfCheckType::kRemoval: {
      auto& r = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRemoval);
      r.set_limit = true;
      r.limit = v1;
      auto& rr = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecrem);
      rr.set_limit2 = true;
      rr.limit2 = v1;
      break;
    }
    case SdfCheckType::kRecrem: {
      auto& r = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecovery);
      r.set_limit = true;
      r.limit = v1;
      auto& rm = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRemoval);
      rm.set_limit = true;
      rm.limit = v2;
      auto& rr = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecrem);
      rr.set_limit = true;
      rr.limit = v1;
      rr.set_limit2 = true;
      rr.limit2 = v2;
      break;
    }
    default:
      break;
  }
}

void PopulateSdfTcSkewWidthPeriod(std::vector<SdfTcAnnotation>& targets,
                                  const SdfTimingCheck& tc,
                                  SdfCheckType check_type, uint64_t v1,
                                  uint64_t v2) {
  switch (check_type) {
    case SdfCheckType::kSkew: {
      auto& s = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSkew);
      s.set_limit = true;
      s.limit = v1;
      auto& ts = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kTimeskew);
      ts.set_limit = true;
      ts.limit = v1;
      break;
    }
    case SdfCheckType::kBidirectskew: {
      auto& fs = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kFullskew);
      fs.set_limit = true;
      fs.limit = v1;
      fs.set_limit2 = true;
      fs.limit2 = v2;
      break;
    }
    case SdfCheckType::kWidth: {
      auto& w = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kWidth);
      w.set_limit = true;
      w.limit = v1;
      break;
    }
    case SdfCheckType::kPeriod: {
      auto& p = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kPeriod);
      p.set_limit = true;
      p.limit = v1;
      break;
    }
    case SdfCheckType::kNochange: {
      auto& nc = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kNochange);
      nc.set_start_edge_offset = true;
      nc.start_edge_offset = static_cast<int64_t>(v1);
      nc.set_end_edge_offset = true;
      nc.end_edge_offset = static_cast<int64_t>(v2);
      break;
    }
    default:
      break;
  }
}

}  // namespace

static std::vector<SdfTcAnnotation> ExpandSdfTimingCheckTargets(
    const SdfTimingCheck& tc, SdfMtm mtm) {
  const uint64_t kV1 = SelectMtm(tc.limit, mtm);
  const uint64_t kV2 = SelectMtm(tc.limit2, mtm);
  std::vector<SdfTcAnnotation> targets;
  switch (tc.check_type) {
    case SdfCheckType::kSetup:
    case SdfCheckType::kHold:
    case SdfCheckType::kSetuphold:
      PopulateSdfTcSetupHold(targets, tc, tc.check_type, kV1, kV2);
      break;
    case SdfCheckType::kRecovery:
    case SdfCheckType::kRemoval:
    case SdfCheckType::kRecrem:
      PopulateSdfTcRecRem(targets, tc, tc.check_type, kV1, kV2);
      break;
    case SdfCheckType::kSkew:
    case SdfCheckType::kBidirectskew:
    case SdfCheckType::kWidth:
    case SdfCheckType::kPeriod:
    case SdfCheckType::kNochange:
      PopulateSdfTcSkewWidthPeriod(targets, tc, tc.check_type, kV1, kV2);
      break;
  }
  return targets;
}

static bool CellInScope(std::string_view instance, std::string_view scope) {
  if (scope.empty()) return true;
  if (instance.size() < scope.size()) return false;
  if (instance.compare(0, scope.size(), scope) != 0) return false;
  if (instance.size() == scope.size()) return true;
  const char kSep = instance[scope.size()];
  return kSep == '/' || kSep == '.';
}

namespace {

// Builds the implicit delay-entry ordering used when a cell does not carry an
// explicit one: all iopaths, then pulse limits, then interconnects.
std::vector<SdfDelayEntryRef> BuildDerivedSdfDelayOrder(const SdfCell& cell) {
  std::vector<SdfDelayEntryRef> derived;
  derived.reserve(cell.iopaths.size() + cell.pulse_limits.size() +
                  cell.interconnects.size());
  for (uint32_t i = 0; i < cell.iopaths.size(); ++i) {
    derived.push_back({SdfDelayEntryKind::kIopath, i});
  }
  for (uint32_t i = 0; i < cell.pulse_limits.size(); ++i) {
    derived.push_back({SdfDelayEntryKind::kPulseLimit, i});
  }
  for (uint32_t i = 0; i < cell.interconnects.size(); ++i) {
    derived.push_back({SdfDelayEntryKind::kInterconnect, i});
  }
  return derived;
}

// Fills the 12 path-delay slots of `pd` from the iopath's rise/fall/turnoff
// delay values.
void FillSdfIopathDelays(PathDelay& pd, const SdfIopath& io, SdfMtm mtm) {
  const auto kExpanded = ExpandSdfDelays({io.rise, io.fall, io.turnoff}, mtm);
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) pd.delays[i] = kExpanded[i];
}

// Handles the non-extended (legacy) iopath form: increment in place, or apply
// the global pulse limits and add. Returns once the entry is committed.
void AnnotateSdfIopathSimple(PathDelay& pd, const SdfIopath& io,
                             SpecifyManager& mgr) {
  if (io.is_increment) {
    mgr.IncrementPathDelay(pd);
    return;
  }
  ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                         mgr.ErrorPulseLimitPercent());
  mgr.AddPathDelay(pd);
}

// Applies the explicit reject/error pulse limits supplied with an extended-form
// iopath onto the already-built path delay.
void ApplySdfIopathPulseLimits(PathDelay& pd, const SdfIopath& io,
                               SpecifyManager& mgr, SdfMtm mtm) {
  ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                         mgr.ErrorPulseLimitPercent());
  if (io.rise_reject_present || io.fall_reject_present) {
    const SdfDelayValue& src_dv =
        io.rise_reject_present ? io.rise_reject : io.fall_reject;
    const uint64_t kReject = SelectMtm(src_dv, mtm);
    for (int i = 0; i < 12; ++i) pd.reject_limit[i] = kReject;
  }
  if (io.rise_error_present || io.fall_error_present) {
    const SdfDelayValue& src_dv =
        io.rise_error_present ? io.rise_error : io.fall_error;
    const uint64_t kErr = SelectMtm(src_dv, mtm);
    for (int i = 0; i < 12; ++i) pd.error_limit[i] = kErr;
  }
}

// Handles the extended iopath form: with no supplied pulse limits it is added
// as-is, otherwise the explicit limits are applied first.
void AnnotateSdfIopathExtended(PathDelay& pd, const SdfIopath& io,
                               SpecifyManager& mgr, SdfMtm mtm) {
  const bool kAnyPulseSupplied =
      io.rise_reject_present || io.rise_error_present ||
      io.fall_reject_present || io.fall_error_present;
  if (!kAnyPulseSupplied) {
    mgr.AddPathDelay(pd, true);
    return;
  }
  ApplySdfIopathPulseLimits(pd, io, mgr, mtm);
  mgr.AddPathDelay(pd);
}

void AnnotateSdfIopathEntry(const SdfIopath& io, SpecifyManager& mgr,
                            SdfMtm mtm) {
  PathDelay pd;
  pd.src_port = io.src_port;
  pd.dst_port = io.dst_port;

  pd.condition = io.condition;
  pd.is_ifnone = io.is_ifnone;

  FillSdfIopathDelays(pd, io, mtm);
  if (!io.extended_form) {
    AnnotateSdfIopathSimple(pd, io, mgr);
    return;
  }
  AnnotateSdfIopathExtended(pd, io, mgr, mtm);
}

void AnnotateSdfInterconnectEntry(const SdfInterconnect& ic,
                                  SpecifyManager& mgr, SdfMtm mtm) {
  InterconnectDelay delay;
  delay.src_port = ic.src_port;
  delay.dst_port = ic.dst_port;
  delay.rise = SelectMtm(ic.rise, mtm);
  delay.fall = SelectMtm(ic.fall, mtm);

  const bool kFallSupplied =
      ic.fall.min_val != 0 || ic.fall.typ_val != 0 || ic.fall.max_val != 0;
  std::vector<SdfDelayValue> ic_vals;
  ic_vals.push_back(ic.rise);
  if (kFallSupplied) ic_vals.push_back(ic.fall);
  const auto kExpanded = ExpandSdfDelays(ic_vals, mtm);
  for (int i = 0; i < 12; ++i) {
    delay.delays[i] = kExpanded[i];

    delay.reject_limit[i] = kExpanded[i];
    delay.error_limit[i] = kExpanded[i];
  }

  if (ic.is_increment) {
    mgr.IncrementInterconnectDelay(delay);
    return;
  }
  mgr.AddInterconnectDelay(std::move(delay));
}

void AnnotateSdfDelayEntry(const SdfCell& cell, const SdfDelayEntryRef& entry,
                           SpecifyManager& mgr, SdfMtm mtm) {
  switch (entry.kind) {
    case SdfDelayEntryKind::kIopath:
      AnnotateSdfIopathEntry(cell.iopaths[entry.index], mgr, mtm);
      break;
    case SdfDelayEntryKind::kPulseLimit: {
      const auto& pl = cell.pulse_limits[entry.index];
      mgr.AddSdfPulseLimit(pl.src_port, pl.dst_port, SelectMtm(pl.reject, mtm),
                           pl.has_error, SelectMtm(pl.error, mtm),
                           pl.is_percent);
      break;
    }
    case SdfDelayEntryKind::kInterconnect:
      AnnotateSdfInterconnectEntry(cell.interconnects[entry.index], mgr, mtm);
      break;
  }
}

void AnnotateSdfSpecparams(const SdfCell& cell, SpecifyManager& mgr,
                           SdfMtm mtm) {
  for (const auto& sp : cell.specparams) {
    SpecparamValue value;
    value.name = sp.name;
    value.value = SelectMtm(sp.value, mtm);

    if (sp.is_increment) {
      mgr.IncrementSpecparamValue(std::move(value));
    } else {
      mgr.SetSpecparamValue(std::move(value));
    }
  }
}

void AnnotateSdfCell(const SdfCell& cell, SpecifyManager& mgr, SdfMtm mtm) {
  std::vector<SdfDelayEntryRef> derived;
  const std::vector<SdfDelayEntryRef>* order = &cell.delay_entry_order;
  if (order->empty() && (!cell.iopaths.empty() || !cell.pulse_limits.empty() ||
                         !cell.interconnects.empty())) {
    derived = BuildDerivedSdfDelayOrder(cell);
    order = &derived;
  }
  for (const auto& entry : *order) {
    AnnotateSdfDelayEntry(cell, entry, mgr, mtm);
  }
  AnnotateSdfSpecparams(cell, mgr, mtm);
  for (const auto& tc : cell.timing_checks) {
    for (const auto& target : ExpandSdfTimingCheckTargets(tc, mtm)) {
      mgr.AnnotateSdfTimingCheck(target);
    }
  }
}

}  // namespace

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view scope) {
  SdfAnnotationResult result;

  for (const auto& kw : file.unannotatable) {
    result.warnings.push_back("SDF annotator: unable to annotate " + kw +
                              " construct");
  }

  for (const auto& cell : file.cells) {
    if (!CellInScope(cell.instance, scope)) continue;
    AnnotateSdfCell(cell, mgr, mtm);
  }
  return result;
}

bool ParseSdfMtmKeyword(std::string_view text, SdfMtmKeyword& out) {
  if (text == "MAXIMUM") {
    out = SdfMtmKeyword::kMaximum;
    return true;
  }
  if (text == "MINIMUM") {
    out = SdfMtmKeyword::kMinimum;
    return true;
  }
  if (text == "TYPICAL") {
    out = SdfMtmKeyword::kTypical;
    return true;
  }
  if (text == "TOOL_CONTROL") {
    out = SdfMtmKeyword::kToolControl;
    return true;
  }
  return false;
}

SdfMtm ResolveSdfMtm(SdfMtmKeyword keyword, SdfMtm tool_default) {
  switch (keyword) {
    case SdfMtmKeyword::kMaximum:
      return SdfMtm::kMaximum;
    case SdfMtmKeyword::kMinimum:
      return SdfMtm::kMinimum;
    case SdfMtmKeyword::kTypical:
      return SdfMtm::kTypical;
    case SdfMtmKeyword::kToolControl:
      return tool_default;
  }
  return tool_default;
}

bool ParseSdfScaleType(std::string_view text, SdfScaleType& out) {
  if (text == "FROM_MTM") {
    out = SdfScaleType::kFromMtm;
    return true;
  }
  if (text == "FROM_MAXIMUM") {
    out = SdfScaleType::kFromMaximum;
    return true;
  }
  if (text == "FROM_MINIMUM") {
    out = SdfScaleType::kFromMinimum;
    return true;
  }
  if (text == "FROM_TYPICAL") {
    out = SdfScaleType::kFromTypical;
    return true;
  }
  return false;
}

static bool ParseRealAt(std::string_view text, std::size_t& pos, double& out) {
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  std::size_t start = pos;
  if (pos < text.size() && (text[pos] == '+' || text[pos] == '-')) ++pos;
  bool saw_digit = false;
  while (pos < text.size() &&
         std::isdigit(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
    saw_digit = true;
  }
  if (pos < text.size() && text[pos] == '.') {
    ++pos;
    while (pos < text.size() &&
           std::isdigit(static_cast<unsigned char>(text[pos])) != 0) {
      ++pos;
      saw_digit = true;
    }
  }
  if (!saw_digit) return false;
  out = std::stod(std::string(text.substr(start, pos - start)));
  return true;
}

bool ParseSdfScaleFactors(std::string_view text, SdfScaleFactors& out) {
  out = SdfScaleFactors{};
  if (text.empty()) return true;
  std::size_t pos = 0;
  double v = 0.0;
  if (!ParseRealAt(text, pos, v)) return false;
  out.min_factor = v;
  out.typ_factor = v;
  out.max_factor = v;
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  if (pos >= text.size() || text[pos] != ':') return true;
  ++pos;
  if (!ParseRealAt(text, pos, v)) return false;
  out.typ_factor = v;
  out.max_factor = v;
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  if (pos >= text.size() || text[pos] != ':') return true;
  ++pos;
  if (!ParseRealAt(text, pos, v)) return false;
  out.max_factor = v;
  return true;
}

static uint64_t RoundToTicks(double scaled) {
  if (scaled <= 0.0) return 0;
  return static_cast<uint64_t>(std::floor(scaled + 0.5));
}

SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors) {
  double src_min = 0.0;
  double src_typ = 0.0;
  double src_max = 0.0;
  switch (type) {
    case SdfScaleType::kFromMtm:
      src_min = static_cast<double>(value.min_val);
      src_typ = static_cast<double>(value.typ_val);
      src_max = static_cast<double>(value.max_val);
      break;
    case SdfScaleType::kFromMinimum:
      src_min = src_typ = src_max = static_cast<double>(value.min_val);
      break;
    case SdfScaleType::kFromTypical:
      src_min = src_typ = src_max = static_cast<double>(value.typ_val);
      break;
    case SdfScaleType::kFromMaximum:
      src_min = src_typ = src_max = static_cast<double>(value.max_val);
      break;
  }
  SdfDelayValue out;
  out.min_val = RoundToTicks(src_min * factors.min_factor);
  out.typ_val = RoundToTicks(src_typ * factors.typ_factor);
  out.max_val = RoundToTicks(src_max * factors.max_factor);
  return out;
}

SdfFile ScaleSdfFile(const SdfFile& file, SdfScaleType type,
                     const SdfScaleFactors& factors) {
  SdfFile out = file;
  for (auto& cell : out.cells) {
    for (auto& io : cell.iopaths) {
      io.rise = ApplySdfScaling(io.rise, type, factors);
      io.fall = ApplySdfScaling(io.fall, type, factors);
      io.turnoff = ApplySdfScaling(io.turnoff, type, factors);
      io.rise_reject = ApplySdfScaling(io.rise_reject, type, factors);
      io.rise_error = ApplySdfScaling(io.rise_error, type, factors);
      io.fall_reject = ApplySdfScaling(io.fall_reject, type, factors);
      io.fall_error = ApplySdfScaling(io.fall_error, type, factors);
    }
    for (auto& tc : cell.timing_checks) {
      tc.limit = ApplySdfScaling(tc.limit, type, factors);
      tc.limit2 = ApplySdfScaling(tc.limit2, type, factors);
    }
    for (auto& sp : cell.specparams) {
      sp.value = ApplySdfScaling(sp.value, type, factors);
    }
    for (auto& ic : cell.interconnects) {
      ic.rise = ApplySdfScaling(ic.rise, type, factors);
      ic.fall = ApplySdfScaling(ic.fall, type, factors);
    }
    for (auto& pl : cell.pulse_limits) {
      pl.reject = ApplySdfScaling(pl.reject, type, factors);
      pl.error = ApplySdfScaling(pl.error, type, factors);
    }
  }
  return out;
}

bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path) {
  if (log_path.empty()) return true;
  std::ofstream out{std::string(log_path)};
  if (!out.is_open()) return false;

  for (const auto& cell : file.cells) {
    const std::string kPrefix = cell.cell_type + "/" + cell.instance + ": ";
    for (const auto& io : cell.iopaths) {
      out << kPrefix << "IOPATH " << io.src_port << " -> " << io.dst_port
          << " rise=" << io.rise.typ_val << " fall=" << io.fall.typ_val << '\n';
    }
    for (const auto& ic : cell.interconnects) {
      out << kPrefix << "INTERCONNECT " << ic.src_port << " -> " << ic.dst_port
          << " rise=" << ic.rise.typ_val << " fall=" << ic.fall.typ_val << '\n';
    }
    for (const auto& pl : cell.pulse_limits) {
      out << kPrefix << "PATHPULSE " << pl.src_port << " -> " << pl.dst_port
          << " reject=" << pl.reject.typ_val << " error=" << pl.error.typ_val
          << '\n';
    }
    for (const auto& tc : cell.timing_checks) {
      out << kPrefix << "TIMINGCHECK " << tc.data_port << " ref=" << tc.ref_port
          << " limit=" << tc.limit.typ_val << '\n';
    }
    for (const auto& sp : cell.specparams) {
      out << kPrefix << "SPECPARAM " << sp.name << " value=" << sp.value.typ_val
          << '\n';
    }
  }
  return true;
}

ResolvedSdfAnnotateArgs ResolveSdfAnnotateArgs(
    std::string_view explicit_mtm_spec, std::string_view explicit_scale_factors,
    std::string_view explicit_scale_type, const SdfAnnotateConfig& config) {
  ResolvedSdfAnnotateArgs out;

  if (!config.mtm_spec.empty()) {
    ParseSdfMtmKeyword(config.mtm_spec, out.mtm);
  }
  if (!explicit_mtm_spec.empty()) {
    ParseSdfMtmKeyword(explicit_mtm_spec, out.mtm);
  }

  if (!config.scale_factors.empty()) {
    ParseSdfScaleFactors(config.scale_factors, out.factors);
  }
  if (!explicit_scale_factors.empty()) {
    ParseSdfScaleFactors(explicit_scale_factors, out.factors);
  }

  if (!config.scale_type.empty()) {
    ParseSdfScaleType(config.scale_type, out.scale_type);
  }
  if (!explicit_scale_type.empty()) {
    ParseSdfScaleType(explicit_scale_type, out.scale_type);
  }

  return out;
}

}  // namespace delta
