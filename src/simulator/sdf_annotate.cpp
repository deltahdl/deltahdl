#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <fstream>
#include <initializer_list>
#include <sstream>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
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

namespace {

// The six explicit SDF delay-transition values supplied for the 6-tuple delay
// form (IEEE 1800 SDF annotation): 0->1, 1->0, 0->Z, Z->1, 1->Z, Z->0. They
// together describe one domain object - a single delay specification - so they
// travel as one struct rather than six loose scalars.
struct SdfSixDelays {
  uint64_t v1;
  uint64_t v2;
  uint64_t v3;
  uint64_t v4;
  uint64_t v5;
  uint64_t v6;
};

}  // namespace

static void ExpandSdfDelaysSixDirect(std::vector<uint64_t>& out,
                                     const SdfSixDelays& d) {
  out[0] = d.v1;
  out[1] = d.v2;
  out[2] = d.v3;
  out[3] = d.v4;
  out[4] = d.v5;
  out[5] = d.v6;
}

static void ExpandSdfDelaysSixDerived(std::vector<uint64_t>& out,
                                      const SdfSixDelays& d) {
  out[6] = std::min(d.v1, d.v3);
  out[7] = std::max(d.v1, d.v4);
  out[8] = std::min(d.v2, d.v5);
  out[9] = std::max(d.v2, d.v6);
  out[10] = std::max(d.v3, d.v5);
  out[11] = std::min(d.v4, d.v6);
}

static void ExpandSdfDelaysSix(std::vector<uint64_t>& out,
                               const SdfSixDelays& d) {
  ExpandSdfDelaysSixDirect(out, d);
  ExpandSdfDelaysSixDerived(out, d);
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
    ExpandSdfDelaysSix(out, SdfSixDelays{kV1, kV2, kV3, kV4, kV5, kV6});
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

// §32.9: a module_instance operand names a level of the design hierarchy, and
// the annotator works from that level down. A SystemVerilog hierarchical name
// divides its levels with '.' while an SDF instance path divides them with '/',
// so the two are compared level by level with either divider accepted rather
// than as raw text.
static bool CellInScope(std::string_view instance, std::string_view scope) {
  if (scope.empty()) return true;
  if (instance.size() < scope.size()) return false;
  for (std::size_t i = 0; i < scope.size(); ++i) {
    const char kInst = instance[i];
    const char kScope = scope[i];
    const bool kBothDividers =
        (kInst == '/' || kInst == '.') && (kScope == '/' || kScope == '.');
    if (kInst != kScope && !kBothDividers) return false;
  }
  if (instance.size() == scope.size()) return true;
  const char kSep = instance[scope.size()];
  return kSep == '/' || kSep == '.';
}

namespace {

// Builds the implicit construct ordering used when a cell does not carry an
// explicit one, as a cell assembled in memory rather than parsed does not:
// all iopaths, then pulse limits, then interconnects, devices, specparams and
// timing checks.
std::vector<SdfCellEntryRef> BuildDerivedSdfCellOrder(const SdfCell& cell) {
  std::vector<SdfCellEntryRef> derived;
  derived.reserve(cell.iopaths.size() + cell.pulse_limits.size() +
                  cell.interconnects.size() + cell.devices.size() +
                  cell.specparams.size() + cell.timing_checks.size());
  for (uint32_t i = 0; i < cell.iopaths.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kIopath, i});
  }
  for (uint32_t i = 0; i < cell.pulse_limits.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kPulseLimit, i});
  }
  for (uint32_t i = 0; i < cell.interconnects.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kInterconnect, i});
  }
  for (uint32_t i = 0; i < cell.devices.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kDevice, i});
  }
  for (uint32_t i = 0; i < cell.specparams.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kSpecparam, i});
  }
  for (uint32_t i = 0; i < cell.timing_checks.size(); ++i) {
    derived.push_back({SdfCellEntryKind::kTimingCheck, i});
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
    mgr.IncrementSdfPathDelay(pd);
    return;
  }
  ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                         mgr.ErrorPulseLimitPercent());
  mgr.AnnotateSdfPathDelay(pd);
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

// §32.5: an extended iopath writes each of its two pulse limits either as a
// value or as an empty pair of parentheses, and an empty one holds whatever the
// path already carries rather than overwriting it. The two limits are decided
// separately, so an entry may supply a reject limit and hold the error limit,
// or the other way round, as well as hold both or supply both.
PathDelayPulseRetention SdfIopathPulseRetention(const SdfIopath& io) {
  PathDelayPulseRetention retain;
  retain.reject = !io.rise_reject_present && !io.fall_reject_present;
  retain.error = !io.rise_error_present && !io.fall_error_present;
  return retain;
}

// Handles the extended iopath form: the limits it supplies are applied, and the
// ones it left empty are held at their current values.
void AnnotateSdfIopathExtended(PathDelay& pd, const SdfIopath& io,
                               SpecifyManager& mgr, SdfMtm mtm) {
  ApplySdfIopathPulseLimits(pd, io, mgr, mtm);
  mgr.AnnotateSdfPathDelay(pd, SdfIopathPulseRetention(io));
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

// §32.4.4 Table 32-3: the SystemVerilog structure all three rows annotate is an
// interconnect delay, but each row names its target its own way, so the row is
// carried across to the manager, which owns the rules for finding it.
SdfInterconnectConstruct SdfInterconnectConstructOf(SdfInterconnectKind kind) {
  switch (kind) {
    case SdfInterconnectKind::kPort:
      return SdfInterconnectConstruct::kPort;
    case SdfInterconnectKind::kNetdelay:
      return SdfInterconnectConstruct::kNetdelay;
    case SdfInterconnectKind::kInterconnect:
      break;
  }
  return SdfInterconnectConstruct::kInterconnect;
}

std::string_view SdfInterconnectKeyword(SdfInterconnectKind kind) {
  switch (kind) {
    case SdfInterconnectKind::kPort:
      return "PORT";
    case SdfInterconnectKind::kNetdelay:
      return "NETDELAY";
    case SdfInterconnectKind::kInterconnect:
      break;
  }
  return "INTERCONNECT";
}

// §32.4.4 Table 32-3 footnote: NETDELAY belongs to OVI SDF 1.0, 2.0 and 2.1 and
// to IEEE SDF 4.0. A file that declares any other version carries no NETDELAY
// construct, so one found there is data the annotator will not take in. A file
// that declares no version at all is left alone.
bool SdfVersionHasNetdelay(std::string_view version) {
  if (version.empty()) return true;
  for (std::string_view known : {"1.0", "2.0", "2.1", "4.0"}) {
    if (version.find(known) != std::string_view::npos) return true;
  }
  return false;
}

void AnnotateSdfInterconnectEntry(const SdfInterconnect& ic,
                                  const SdfFile& file, SpecifyManager& mgr,
                                  SdfMtm mtm, SdfAnnotationResult& result) {
  if (ic.kind == SdfInterconnectKind::kNetdelay &&
      !SdfVersionHasNetdelay(file.version)) {
    result.warnings.push_back(
        "SDF annotator: unable to annotate NETDELAY construct, which SDF "
        "version " +
        file.version + " does not define");
    return;
  }

  SdfInterconnectAnnotation ann;
  ann.source = ic.src_port;
  ann.load = ic.dst_port;
  ann.construct = SdfInterconnectConstructOf(ic.kind);
  ann.is_increment = ic.is_increment;

  // §32.4.4: interconnect delays fill in their twelve transition delays from
  // the values the entry lists exactly the way a specify path delay does.
  std::vector<SdfDelayValue> ic_vals = ic.values;
  if (ic_vals.empty()) {
    const bool kFallSupplied =
        ic.fall.min_val != 0 || ic.fall.typ_val != 0 || ic.fall.max_val != 0;
    ic_vals.push_back(ic.rise);
    if (kFallSupplied) ic_vals.push_back(ic.fall);
  }
  const auto kExpanded = ExpandSdfDelays(ic_vals, mtm);
  for (int i = 0; i < 12; ++i) ann.delays[i] = kExpanded[i];

  SdfInterconnectOutcome outcome = mgr.AnnotateSdfInterconnect(ann);
  for (auto& warning : outcome.warnings) {
    result.warnings.push_back(std::move(warning));
  }
  // §32.3: an entry the annotator understood but could not place anywhere is
  // reported rather than dropped in silence.
  if (!outcome.annotated && outcome.warnings.empty()) {
    result.warnings.push_back("SDF annotator: unable to annotate " +
                              std::string(SdfInterconnectKeyword(ic.kind)) +
                              " delay on " + ic.dst_port);
  }
}

// §32.4.1 Table 32-1: hand one DEVICE entry to the manager, which decides which
// module outputs it reaches. An entry that reaches nothing at all is data the
// annotator understood but could not place, so it is warned about (§32.3).
void AnnotateSdfDeviceEntry(const SdfDevice& dev, SpecifyManager& mgr,
                            SdfMtm mtm, SdfAnnotationResult& result) {
  SdfDeviceAnnotation ann;
  ann.port_instance = dev.port_instance;
  ann.is_increment = dev.is_increment;
  const auto kExpanded =
      ExpandSdfDelays({dev.rise, dev.fall, dev.turnoff}, mtm);
  for (int i = 0; i < 12; ++i) ann.delays[i] = kExpanded[i];

  if (mgr.AnnotateSdfDeviceDelay(ann)) return;
  const std::string kTarget = dev.port_instance.empty()
                                  ? std::string("module outputs")
                                  : dev.port_instance;
  result.warnings.push_back(
      "SDF annotator: unable to annotate DEVICE delay on " + kTarget);
}

void AnnotateSdfSpecparamEntry(const SdfSpecparam& sp, SpecifyManager& mgr,
                               SdfMtm mtm) {
  SpecparamValue value;
  value.name = sp.name;
  value.value = SelectMtm(sp.value, mtm);

  if (sp.is_increment) {
    mgr.IncrementSpecparamValue(std::move(value));
  } else {
    mgr.SetSpecparamValue(std::move(value));
  }
}

// The SDF keyword a check came in under, so a warning about it names the same
// construct the file's author wrote.
std::string_view SdfCheckTypeName(SdfCheckType type) {
  switch (type) {
    case SdfCheckType::kSetup:
      return "SETUP";
    case SdfCheckType::kHold:
      return "HOLD";
    case SdfCheckType::kSetuphold:
      return "SETUPHOLD";
    case SdfCheckType::kRecovery:
      return "RECOVERY";
    case SdfCheckType::kRemoval:
      return "REMOVAL";
    case SdfCheckType::kRecrem:
      return "RECREM";
    case SdfCheckType::kWidth:
      return "WIDTH";
    case SdfCheckType::kPeriod:
      return "PERIOD";
    case SdfCheckType::kSkew:
      return "SKEW";
    case SdfCheckType::kBidirectskew:
      return "BIDIRECTSKEW";
    case SdfCheckType::kNochange:
      return "NOCHANGE";
  }
  return "timing";
}

void AnnotateSdfTimingCheckEntry(const SdfTimingCheck& tc, SpecifyManager& mgr,
                                 SdfMtm mtm, SdfAnnotationResult& result) {
  // An SDF check offers several candidate annotations so it can update
  // whichever form the specify block happens to declare; landing any one of
  // them means the constraint was placed.
  bool placed = false;
  for (const auto& target : ExpandSdfTimingCheckTargets(tc, mtm)) {
    if (mgr.AnnotateSdfTimingCheck(target)) placed = true;
  }
  // §32.3: a constraint the design declares no check for is data the annotator
  // understood but could not put anywhere, so it warns rather than dropping the
  // value in silence. Timing checks are the only category that can fail this
  // way -- delays and specparams that match nothing are simply recorded.
  if (placed) return;
  result.warnings.push_back("SDF annotator: unable to annotate " +
                            std::string(SdfCheckTypeName(tc.check_type)) +
                            " timing check on " + tc.ref_port + "/" +
                            tc.data_port);
}

void AnnotateSdfCellEntry(const SdfCell& cell, const SdfFile& file,
                          const SdfCellEntryRef& entry, SpecifyManager& mgr,
                          SdfMtm mtm, SdfAnnotationResult& result) {
  switch (entry.kind) {
    case SdfCellEntryKind::kIopath:
      AnnotateSdfIopathEntry(cell.iopaths[entry.index], mgr, mtm);
      break;
    case SdfCellEntryKind::kPulseLimit: {
      const auto& pl = cell.pulse_limits[entry.index];
      mgr.AddSdfPulseLimit(SdfPulseLimitSpec{
          /*src=*/pl.src_port,
          /*dst=*/pl.dst_port,
          /*reject=*/SelectMtm(pl.reject, mtm),
          /*error=*/SelectMtm(pl.error, mtm),
          /*has_error=*/pl.has_error,
          /*is_percent=*/pl.is_percent,
      });
      break;
    }
    case SdfCellEntryKind::kInterconnect:
      AnnotateSdfInterconnectEntry(cell.interconnects[entry.index], file, mgr,
                                   mtm, result);
      break;
    case SdfCellEntryKind::kDevice:
      AnnotateSdfDeviceEntry(cell.devices[entry.index], mgr, mtm, result);
      break;
    case SdfCellEntryKind::kSpecparam:
      AnnotateSdfSpecparamEntry(cell.specparams[entry.index], mgr, mtm);
      break;
    case SdfCellEntryKind::kTimingCheck:
      AnnotateSdfTimingCheckEntry(cell.timing_checks[entry.index], mgr, mtm,
                                  result);
      break;
  }
}

// §32.5: annotation is an ordered process, so a cell's constructs are applied
// one after another in the order the file wrote them -- across the cell's
// sections, not merely within each one. That is what lets a construct's
// annotation be overwritten or modified by a later construct of a different
// kind: a LABEL that reprices a specparam a module path delay expression reads
// undoes an earlier IOPATH on that path, and an IOPATH written after the LABEL
// undoes the LABEL's effect on that path instead.
void AnnotateSdfCell(const SdfCell& cell, const SdfFile& file,
                     SpecifyManager& mgr, SdfMtm mtm,
                     SdfAnnotationResult& result) {
  std::vector<SdfCellEntryRef> derived;
  const std::vector<SdfCellEntryRef>* order = &cell.entry_order;
  if (order->empty()) {
    derived = BuildDerivedSdfCellOrder(cell);
    order = &derived;
  }
  for (const auto& entry : *order) {
    AnnotateSdfCellEntry(cell, file, entry, mgr, mtm, result);
  }
}

}  // namespace

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view scope) {
  SdfAnnotationResult result;

  // §32.3: every piece of SDF data the annotator could not take in gets its own
  // warning. The parser collects them as it goes; constructs that carry no
  // SystemVerilog timing at all (the TIMINGENV section being the stock example)
  // never reach this list, because those are to be dropped silently.
  for (const auto& kw : file.unannotatable) {
    result.warnings.push_back("SDF annotator: unable to annotate " + kw +
                              " construct");
  }

  // §32.3: annotation is driven purely by what the file supplies. Nothing here
  // walks the manager's existing values, so a timing value the file says
  // nothing about keeps whatever it held before backannotation.
  for (const auto& cell : file.cells) {
    if (!CellInScope(cell.instance, scope)) continue;
    AnnotateSdfCell(cell, file, mgr, mtm, result);
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
      for (auto& v : ic.values) v = ApplySdfScaling(v, type, factors);
    }
    for (auto& pl : cell.pulse_limits) {
      pl.reject = ApplySdfScaling(pl.reject, type, factors);
      pl.error = ApplySdfScaling(pl.error, type, factors);
    }
    for (auto& dev : cell.devices) {
      dev.rise = ApplySdfScaling(dev.rise, type, factors);
      dev.fall = ApplySdfScaling(dev.fall, type, factors);
      dev.turnoff = ApplySdfScaling(dev.turnoff, type, factors);
    }
  }
  return out;
}

// §32.9: every individual annotation the file carries earns its own entry in
// the log file. §32.6 lets several SDF files be annotated in turn, and a later
// call naming the same log file adds its entries to the ones already there
// rather than replacing them, so the log reads as the record of the whole run.
bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path,
                           std::string_view scope) {
  if (log_path.empty()) return true;
  std::ofstream out{std::string(log_path), std::ios::app};
  if (!out.is_open()) return false;

  for (const auto& cell : file.cells) {
    // §32.9: the log records the annotations that were made, and a cell outside
    // the region the call named is never annotated, so it earns no entry.
    if (!CellInScope(cell.instance, scope)) continue;
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
    // A DEVICE entry is annotated like any other delay, so it earns an entry of
    // its own. An entry that names no port instance reaches every output of the
    // cell, which is what the empty target stands for here.
    for (const auto& dev : cell.devices) {
      out << kPrefix << "DEVICE "
          << (dev.port_instance.empty() ? "*" : dev.port_instance)
          << " rise=" << dev.rise.typ_val << " fall=" << dev.fall.typ_val
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

bool ReadSdfFile(std::string_view path, SdfFile& out) {
  if (path.empty()) return false;
  std::ifstream in{std::string(path)};
  if (!in.is_open()) return false;
  std::stringstream buffer;
  buffer << in.rdbuf();
  return ParseSdf(buffer.str(), out);
}

namespace {

// One configuration-file line reduced to the keyword it names and the text that
// follows. A line that names nothing leaves `keyword` empty.
struct SdfConfigLine {
  std::string keyword;
  std::string value;
};

SdfConfigLine SplitSdfConfigLine(std::string_view line) {
  // A comment runs to the end of the line, and a trailing ';' closes an entry.
  const std::size_t kComment = line.find('#');
  if (kComment != std::string_view::npos) line = line.substr(0, kComment);
  const std::size_t kSlashes = line.find("//");
  if (kSlashes != std::string_view::npos) line = line.substr(0, kSlashes);
  const std::size_t kSemi = line.find(';');
  if (kSemi != std::string_view::npos) line = line.substr(0, kSemi);

  auto trim = [](std::string_view s) {
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
      s.remove_prefix(1);
    }
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
      s.remove_suffix(1);
    }
    return s;
  };

  line = trim(line);
  SdfConfigLine out;
  if (line.empty()) return out;
  const std::size_t kSplit = line.find_first_of(" \t=");
  if (kSplit == std::string_view::npos) {
    out.keyword = std::string(line);
    return out;
  }
  out.keyword = std::string(line.substr(0, kSplit));
  std::string_view rest = trim(line.substr(kSplit + 1));
  if (!rest.empty() && rest.front() == '=') rest = trim(rest.substr(1));
  // The value may be quoted, as the same text is a quoted argument when it is
  // written on the $sdf_annotate call instead.
  if (rest.size() >= 2 && rest.front() == '"' && rest.back() == '"') {
    rest = rest.substr(1, rest.size() - 2);
  }
  out.value = std::string(rest);
  return out;
}

}  // namespace

// §32.9: the configuration file controls the same aspects of annotation the
// call's own arguments do. The three the call can also name -- MTM_SPEC,
// SCALE_FACTORS and SCALE_TYPE -- are read here; ResolveSdfAnnotateArgs is what
// then lets an argument written on the call override the keyword read here.
bool ReadSdfAnnotateConfigFile(std::string_view path, SdfAnnotateConfig& out) {
  if (path.empty()) return false;
  std::ifstream in{std::string(path)};
  if (!in.is_open()) return false;

  std::string line;
  while (std::getline(in, line)) {
    const SdfConfigLine kEntry = SplitSdfConfigLine(line);
    if (kEntry.keyword == "MTM_SPEC") {
      out.mtm_spec = kEntry.value;
    } else if (kEntry.keyword == "SCALE_FACTORS") {
      out.scale_factors = kEntry.value;
    } else if (kEntry.keyword == "SCALE_TYPE") {
      out.scale_type = kEntry.value;
    }
  }
  return true;
}

SdfAnnotationResult RunSdfAnnotateTask(const SdfAnnotateTaskArgs& args,
                                       SpecifyManager& mgr,
                                       SdfMtm tool_default) {
  SdfAnnotationResult result;

  // §32.6: each call is one annotation of the design from one SDF file, so the
  // call is recorded on the manager whether or not the file turns out to be
  // readable. That record is what makes a run of several calls, each over its
  // own file and its own region, visible as such.
  mgr.AnnotateSdf({args.sdf_file, args.module_instance});

  SdfFile file;
  if (!ReadSdfFile(args.sdf_file, file)) {
    result.warnings.push_back("SDF annotator: unable to read SDF file " +
                              args.sdf_file);
    return result;
  }

  // §32.9: the configuration file is read first, then whichever of mtm_spec,
  // scale_factors and scale_type the call wrote overrides the matching keyword
  // in it.
  SdfAnnotateConfig config;
  if (!args.config_file.empty() &&
      !ReadSdfAnnotateConfigFile(args.config_file, config)) {
    result.warnings.push_back(
        "SDF annotator: unable to read configuration file " + args.config_file);
  }
  const ResolvedSdfAnnotateArgs kResolved = ResolveSdfAnnotateArgs(
      args.mtm_spec, args.scale_factors, args.scale_type, config);

  // §32.9: an mtm_spec or scale_type the annotator does not know is not one of
  // the keywords Table 32-5 / Table 32-6 lists, so it is reported rather than
  // quietly taken as the default it left in place.
  SdfMtmKeyword mtm_probe = SdfMtmKeyword::kToolControl;
  if (!args.mtm_spec.empty() && !ParseSdfMtmKeyword(args.mtm_spec, mtm_probe)) {
    result.warnings.push_back("SDF annotator: unknown mtm_spec " +
                              args.mtm_spec);
  }
  SdfScaleType type_probe = SdfScaleType::kFromMtm;
  if (!args.scale_type.empty() &&
      !ParseSdfScaleType(args.scale_type, type_probe)) {
    result.warnings.push_back("SDF annotator: unknown scale_type " +
                              args.scale_type);
  }

  const SdfFile kScaled =
      ScaleSdfFile(file, kResolved.scale_type, kResolved.factors);
  const SdfMtm kMtm = ResolveSdfMtm(kResolved.mtm, tool_default);
  SdfAnnotationResult annotated =
      AnnotateSdfToManager(kScaled, mgr, kMtm, args.module_instance);
  for (auto& warning : annotated.warnings) {
    result.warnings.push_back(std::move(warning));
  }

  // §32.9: with a log_file named, each individual annotation the file carries
  // is written out as its own entry.
  if (!args.log_file.empty() &&
      !WriteSdfAnnotationLog(kScaled, args.log_file, args.module_instance)) {
    result.warnings.push_back("SDF annotator: unable to write log file " +
                              args.log_file);
  }
  return result;
}

std::string SdfAnnotateScopeName(const Expr* e, SimContext& ctx, Arena& arena) {
  if (e == nullptr) return {};
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      std::string s;
      if (!e->scope_prefix.empty()) {
        s += std::string(e->scope_prefix);
        s += (e->scope_prefix == "$unit") ? "::" : ".";
      }
      s += std::string(e->text);
      return s;
    }
    case ExprKind::kMemberAccess:
      return SdfAnnotateScopeName(e->lhs, ctx, arena) + "." +
             (e->rhs != nullptr ? std::string(e->rhs->text) : std::string());
    case ExprKind::kSelect: {
      // §32.9: array indices are permitted in a module_instance, so an indexed
      // element of an instance array names its own level of the hierarchy. The
      // index is evaluated, which is what lets it be written as anything that
      // reduces to a value rather than only as a plain number.
      std::string s = SdfAnnotateScopeName(e->base, ctx, arena);
      if (e->index == nullptr) return s;
      const uint64_t kIndex = EvalExpr(e->index, ctx, arena).ToUint64();
      return s + "[" + std::to_string(kIndex) + "]";
    }
    default:
      break;
  }
  return std::string(e->text);
}

namespace {

// §32.9: read one operand of a $sdf_annotate call as a character string. An
// operand the call skipped over on its way to a later one is absent here and
// reads as no text at all, which is the same as leaving it off the end.
std::string SdfAnnotateStringArg(const Expr* call, std::size_t index,
                                 SimContext& ctx, Arena& arena) {
  if (index >= call->args.size() || call->args[index] == nullptr) return {};
  return EvalStringArg(call->args[index], ctx, arena);
}

}  // namespace

bool EvalSdfAnnotateTask(const Expr* call, SimContext& ctx, Arena& arena) {
  if (call == nullptr) return false;
  SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return false;

  SdfAnnotateTaskArgs args;
  // §32.9: sdf_file is the one required operand. It is an expression, so it may
  // be written as a string literal, held in a `string` variable, or held in an
  // integral variable whose bytes spell the name.
  args.sdf_file = SdfAnnotateStringArg(call, 0, ctx, arena);
  if (args.sdf_file.empty()) {
    ctx.GetDiag().Error(call->range.start,
                        "$sdf_annotate requires an SDF file name");
    return false;
  }

  // §32.9: module_instance names a level of the design hierarchy rather than a
  // readable value, so it is taken as the name it writes. Left out, the
  // annotator works from the module that holds the call.
  if (call->args.size() > 1 && call->args[1] != nullptr) {
    args.module_instance = SdfAnnotateScopeName(call->args[1], ctx, arena);
  } else {
    args.module_instance = ctx.CurrentScopeName();
  }

  args.config_file = SdfAnnotateStringArg(call, 2, ctx, arena);
  args.log_file = SdfAnnotateStringArg(call, 3, ctx, arena);
  args.mtm_spec = SdfAnnotateStringArg(call, 4, ctx, arena);
  args.scale_factors = SdfAnnotateStringArg(call, 5, ctx, arena);
  args.scale_type = SdfAnnotateStringArg(call, 6, ctx, arena);

  const SdfAnnotationResult kResult = RunSdfAnnotateTask(args, *mgr);
  for (const auto& warning : kResult.warnings) {
    ctx.GetDiag().Warning(call->range.start, warning);
  }
  return true;
}

}  // namespace delta
