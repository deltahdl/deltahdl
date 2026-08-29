#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"

namespace delta {

// Whichever of the three values `mtm` selects, without the sign the file may
// have written in front of it.
static uint64_t SelectMtmMagnitude(const SdfDelayValue& dv, SdfMtm mtm) {
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

// The sign of the value SelectMtmMagnitude picks, so the two travel together.
static bool SelectMtmNegative(const SdfDelayValue& dv, SdfMtm mtm) {
  switch (mtm) {
    case SdfMtm::kMinimum:
      return dv.min_negative;
    case SdfMtm::kTypical:
      return dv.typ_negative;
    case SdfMtm::kMaximum:
      return dv.max_negative;
  }
  return dv.typ_negative;
}

// §32.7: the selected value with the sign the file wrote in front of it, for
// the one annotation that gives a negative value a meaning -- a pulse limit
// changed in INCREMENT mode, where a negative value lowers the limit already in
// place instead of raising it.
static int64_t SelectSignedMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  const auto kMagnitude = static_cast<int64_t>(SelectMtmMagnitude(dv, mtm));
  return SelectMtmNegative(dv, mtm) ? -kMagnitude : kMagnitude;
}

// The selected value as the unsigned quantity the annotator's other targets
// hold -- a propagation delay, a timing constraint limit, a specparam value.
// None of those can carry a negative number, and §30.5.1 puts a delay whose
// expression is negative at zero, so that is where a value written negative
// reads here.
static uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  if (SelectMtmNegative(dv, mtm)) return 0;
  return SelectMtmMagnitude(dv, mtm);
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
bool CellInScope(std::string_view instance, std::string_view scope) {
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

// §32.9: the cells the module_instance operand selects sit at or below the
// level it names, so what tells two of them apart is the part of the SDF
// instance path below that level. PathDelay::inst_prefix names the same thing
// on the SystemVerilog side, in the spelling Lowerer::inst_prefix_ produces,
// so the remainder is rewritten into that spelling here: '/' dividers become
// '.', and a trailing '.' closes it. The scope root itself has no remainder
// and answers empty, which is the prefix a module elaborated as a top carries.
std::string SdfCellInstancePrefix(std::string_view instance,
                                  std::string_view design_root) {
  if (design_root.empty()) return {};
  if (instance == design_root) return {};
  std::string_view rest = instance;
  // A file may write the cell's path from the root or from below it. Strip the
  // root's own segment where it is there, and take what is left as written
  // where it is not.
  if (rest.size() > design_root.size() &&
      rest.substr(0, design_root.size()) == design_root &&
      (rest[design_root.size()] == '/' || rest[design_root.size()] == '.')) {
    rest = rest.substr(design_root.size() + 1);
  }
  std::string prefix(rest);
  for (char& divider : prefix) {
    if (divider == '/') divider = '.';
  }
  if (!prefix.empty()) prefix.push_back('.');
  return prefix;
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

// §32.8: the delay values an iopath entry listed, and only those. Which column
// of Table 32-4 the twelve transition slots are filled from is chosen by how
// many values the entry supplied, so an entry that stopped after its rise value
// must not arrive here padded out to a rise/fall/turnoff triple. A file's entry
// carries the whole list; one assembled in memory rather than parsed carries
// only its three named fields, and is read as the triple those fields spell.
std::vector<SdfDelayValue> SdfIopathDelayValues(const SdfIopath& io) {
  if (!io.values.empty()) return io.values;
  return {io.rise, io.fall, io.turnoff};
}

// §32.8 Table 32-4: fills the 12 path-delay slots of `pd` from the values the
// iopath listed.
void FillSdfIopathDelays(PathDelay& pd, const SdfIopath& io, SdfMtm mtm) {
  const auto kExpanded = ExpandSdfDelays(SdfIopathDelayValues(io), mtm);
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

// §32.7: how much an extended iopath in INCREMENT mode changes each of the two
// pulse limits by. A limit the entry wrote as an empty pair of parentheses is
// one it is not changing, so its amount is zero; one written with a leading
// minus sign lowers the limit rather than raising it. The two are decided
// separately, exactly as the absolute form decides them.
struct SdfIopathPulseIncrement {
  int64_t reject = 0;
  int64_t error = 0;
};

SdfIopathPulseIncrement SdfIopathPulseIncrementOf(const SdfIopath& io,
                                                  SdfMtm mtm) {
  SdfIopathPulseIncrement inc;
  if (io.rise_reject_present || io.fall_reject_present) {
    const SdfDelayValue& reject_dv =
        io.rise_reject_present ? io.rise_reject : io.fall_reject;
    inc.reject = SelectSignedMtm(reject_dv, mtm);
  }
  if (io.rise_error_present || io.fall_error_present) {
    const SdfDelayValue& error_dv =
        io.rise_error_present ? io.rise_error : io.fall_error;
    inc.error = SelectSignedMtm(error_dv, mtm);
  }
  return inc;
}

// §32.7: an extended iopath in INCREMENT mode modifies what the path already
// carries rather than replacing it, on both halves of the entry. Its delay
// values add to the path's delays -- a direction written as an empty pair of
// parentheses adds nothing there -- and its two pulse-limit values add to the
// limits the path already holds. Nothing here derives a limit from the
// percentage settings: those supply a limit a construct did not state, and an
// INCREMENT entry states a change to the limit already in place.
//
// The delays go through IncrementSdfPathDelay and the two limits through
// IncrementSdfPulseLimit, and both match PathDelay::inst_prefix, so the whole
// entry reaches the one instance its cell named.
void AnnotateSdfIopathIncrementExtended(const PathDelay& pd,
                                        const SdfIopath& io,
                                        SpecifyManager& mgr, SdfMtm mtm) {
  mgr.IncrementSdfPathDelay(pd);
  const SdfIopathPulseIncrement kIncrement = SdfIopathPulseIncrementOf(io, mtm);
  mgr.IncrementSdfPulseLimit(pd.src_port, pd.dst_port, kIncrement.reject,
                             kIncrement.error, pd.inst_prefix);
}

// §32.4.1: an IOPATH names its terminals by the cell's own port names, so the
// path it reaches is told from the identically spelled path of another instance
// of the same cell by PathDelay::inst_prefix alone. The prefix the cell's
// CELLINSTANCE gave (SdfCellInstancePrefix) is stamped on here, which is what
// SpecifyManager::AnnotateSdfPathDelay and IncrementSdfPathDelay match on.
void AnnotateSdfIopathEntry(const SdfIopath& io, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm) {
  PathDelay pd;
  pd.src_port = io.src_port;
  pd.dst_port = io.dst_port;
  pd.inst_prefix = inst_prefix;

  pd.condition = io.condition;
  pd.is_ifnone = io.is_ifnone;

  FillSdfIopathDelays(pd, io, mtm);
  if (!io.extended_form) {
    AnnotateSdfIopathSimple(pd, io, mgr);
    return;
  }
  if (io.is_increment) {
    AnnotateSdfIopathIncrementExtended(pd, io, mgr, mtm);
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

// §32.8: the delay values an interconnect entry listed. A file's entry carries
// the whole list; one assembled in memory rather than parsed carries only its
// two named fields, and is read as the pair those fields spell. Which column of
// Table 32-4 the twelve transition slots come from is settled by how many
// values were supplied, so it is never read off a value's size -- a delay of
// zero is one a file states as readily as any other, and an entry that states
// it has supplied that value just the same.
std::vector<SdfDelayValue> SdfInterconnectDelayValues(
    const SdfInterconnect& ic) {
  if (!ic.values.empty()) return ic.values;
  return {ic.rise, ic.fall};
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
  const auto kExpanded = ExpandSdfDelays(SdfInterconnectDelayValues(ic), mtm);
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

// §32.8: the delay values a DEVICE entry listed. A file's entry carries the
// whole list; one assembled in memory rather than parsed carries only its three
// named fields, and is read as the triple those fields spell.
std::vector<SdfDelayValue> SdfDeviceDelayValues(const SdfDevice& dev) {
  if (!dev.values.empty()) return dev.values;
  return {dev.rise, dev.fall, dev.turnoff};
}

// §32.4.1 Table 32-1: hand one DEVICE entry to the manager, which decides which
// module outputs it reaches. An entry that reaches nothing at all is data the
// annotator understood but could not place, so it is warned about (§32.3).
//
// §32.8: a DEVICE delay may land on a specify path, which carries twelve state
// transition delays, or on a gate primitive, which carries three, and the
// manager is the one that finds out which. Both mappings of the entry's values
// therefore travel with it: the Table 32-4 expansion over twelve slots, and the
// reduction to three plus the delay to the x state.
//
// As with AnnotateSdfPulseLimitEntry above, `inst_prefix` is what
// SdfCellInstancePrefix made of the cell's CELLINSTANCE, and it travels beside
// the entry rather than on it because SdfDeviceAnnotation
// (simulator/specify_sdf.h) has no field for it. It is what holds the delay to
// the outputs of the one instance the entry names.
void AnnotateSdfDeviceEntry(const SdfDevice& dev, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm,
                            SdfAnnotationResult& result) {
  SdfDeviceAnnotation ann;
  ann.port_instance = dev.port_instance;
  ann.is_increment = dev.is_increment;
  const std::vector<SdfDelayValue> kValues = SdfDeviceDelayValues(dev);
  const auto kExpanded = ExpandSdfDelays(kValues, mtm);
  for (int i = 0; i < 12; ++i) ann.delays[i] = kExpanded[i];
  const auto kReduced = ReduceSdfDelaysToThree(kValues, mtm);
  for (int i = 0; i < 4; ++i) ann.three_state_delays[i] = kReduced[i];

  if (mgr.AnnotateSdfDeviceDelay(ann, inst_prefix)) return;
  const std::string kTarget = dev.port_instance.empty()
                                  ? std::string("module outputs")
                                  : dev.port_instance;
  result.warnings.push_back(
      "SDF annotator: unable to annotate DEVICE delay on " + kTarget);
}

// §32.7: how one of a pulse-limit entry's two values reads. In INCREMENT mode
// it is an amount that may lower a limit, so the sign the file wrote is kept;
// stated outright it names a limit itself, where a sign has no meaning.
int64_t SdfPulseLimitValue(const SdfDelayValue& dv, SdfMtm mtm,
                           bool is_increment) {
  if (is_increment) return SelectSignedMtm(dv, mtm);
  return static_cast<int64_t>(SelectMtm(dv, mtm));
}

// §32.7: hand over one PATHPULSE or PATHPULSEPERCENT entry, in whichever mode
// the section carrying it was written.
//
// §30.4 names a path's terminals by the module's own port names, so two
// instances of one cell declare paths spelled identically. `inst_prefix` is
// what SdfCellInstancePrefix worked out for the cell, and it travels beside the
// entry rather than on it because SdfPulseLimitSpec (simulator/specify_sdf.h)
// has no field for it. SpecifyManager::AddSdfPulseLimit matches it against
// PathDelay::inst_prefix, so the limits reach the one instance the entry names.
void AnnotateSdfPulseLimitEntry(const SdfPulseLimit& pl,
                                std::string_view inst_prefix,
                                SpecifyManager& mgr, SdfMtm mtm) {
  mgr.AddSdfPulseLimit(
      SdfPulseLimitSpec{
          /*src=*/pl.src_port,
          /*dst=*/pl.dst_port,
          /*reject=*/SdfPulseLimitValue(pl.reject, mtm, pl.is_increment),
          /*error=*/SdfPulseLimitValue(pl.error, mtm, pl.is_increment),
          /*has_error=*/pl.has_error,
          /*is_percent=*/pl.is_percent,
          /*is_increment=*/pl.is_increment,
      },
      inst_prefix);
}

// §32.4.3: hand over one LABEL entry. §30.3 has a specify block declare its
// specparams by bare names, so `inst_prefix` -- SdfCellInstancePrefix's answer
// for the cell, as for the three siblings above -- holds it to that instance.
void AnnotateSdfSpecparamEntry(const SdfSpecparam& sp,
                               std::string_view inst_prefix,
                               SpecifyManager& mgr, SdfMtm mtm) {
  SpecparamValue value;
  value.name = sp.name;
  value.value = SelectMtm(sp.value, mtm);

  if (sp.is_increment) {
    mgr.IncrementSpecparamValue(std::move(value), inst_prefix);
  } else {
    mgr.SetSpecparamValue(std::move(value), inst_prefix);
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

// §32.5: the SDF source one annotation is taken from -- the cell whose entry is
// being applied, the file it sits in, which an INTERCONNECT entry resolves its
// port names against, and the instance prefix the cell's CELLINSTANCE names.
//
// `inst_prefix` is what SdfCellInstancePrefix (simulator/sdf_parser.h) made of
// the cell's instance path against the §32.9 module_instance operand: the
// hierarchical prefix of the module instance whose specify block declared the
// paths this cell annotates, in the spelling PathDelay::inst_prefix carries.
struct SdfCellSource {
  const SdfCell& cell;
  const SdfFile& file;
  std::string_view inst_prefix;
};

void AnnotateSdfCellEntry(const SdfCellSource& src,
                          const SdfCellEntryRef& entry, SpecifyManager& mgr,
                          SdfMtm mtm, SdfAnnotationResult& result) {
  const SdfCell& cell = src.cell;
  switch (entry.kind) {
    case SdfCellEntryKind::kIopath:
      AnnotateSdfIopathEntry(cell.iopaths[entry.index], src.inst_prefix, mgr,
                             mtm);
      break;
    case SdfCellEntryKind::kPulseLimit:
      AnnotateSdfPulseLimitEntry(cell.pulse_limits[entry.index],
                                 src.inst_prefix, mgr, mtm);
      break;
    case SdfCellEntryKind::kInterconnect:
      AnnotateSdfInterconnectEntry(cell.interconnects[entry.index], src.file,
                                   mgr, mtm, result);
      break;
    case SdfCellEntryKind::kDevice:
      AnnotateSdfDeviceEntry(cell.devices[entry.index], src.inst_prefix, mgr,
                             mtm, result);
      break;
    case SdfCellEntryKind::kSpecparam:
      AnnotateSdfSpecparamEntry(cell.specparams[entry.index], src.inst_prefix,
                                mgr, mtm);
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
void AnnotateSdfCell(const SdfCellSource& src, SpecifyManager& mgr, SdfMtm mtm,
                     SdfAnnotationResult& result) {
  std::vector<SdfCellEntryRef> derived;
  const std::vector<SdfCellEntryRef>* order = &src.cell.entry_order;
  if (order->empty()) {
    derived = BuildDerivedSdfCellOrder(src.cell);
    order = &derived;
  }
  for (const auto& entry : *order) {
    AnnotateSdfCellEntry(src, entry, mgr, mtm, result);
  }
}

}  // namespace

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view scope,
                                         std::string_view design_root) {
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
    // §32.9: the operand selected the cell, and the part of its instance path
    // below the operand's level is what says which instance of the cell the
    // entries below annotate. Working it out once here keeps every entry of
    // the cell reading the one answer.
    std::string prefix = SdfCellInstancePrefix(cell.instance, design_root);
    AnnotateSdfCell({cell, file, prefix}, mgr, mtm, result);
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

}  // namespace delta
