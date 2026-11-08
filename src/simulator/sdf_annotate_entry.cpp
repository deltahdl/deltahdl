#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/sdf_annotate_internal.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

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

int64_t SelectSignedMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  const auto kMagnitude = static_cast<int64_t>(SelectMtmMagnitude(dv, mtm));
  return SelectMtmNegative(dv, mtm) ? -kMagnitude : kMagnitude;
}

static double SelectRealMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  double real = dv.typ_real;
  if (mtm == SdfMtm::kMinimum) real = dv.min_real;
  if (mtm == SdfMtm::kMaximum) real = dv.max_real;
  return SelectMtmNegative(dv, mtm) ? -real : real;
}

bool SdfValueHeld(const SdfDelayValue& dv, SdfMtm mtm) {
  if (dv.empty) return true;
  switch (mtm) {
    case SdfMtm::kMinimum:
      return dv.min_empty;
    case SdfMtm::kMaximum:
      return dv.max_empty;
    default:
      return dv.typ_empty;
  }
}

uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  if (SelectMtmNegative(dv, mtm)) return 0;
  return SelectMtmMagnitude(dv, mtm);
}

template <typename T>
static void ExpandSdfDelaysTwo(std::vector<T>& out, T v1, T v2) {
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

template <typename T>
static void ExpandSdfDelaysThree(std::vector<T>& out, T v1, T v2, T v3) {
  out[0] = v1;
  out[1] = v2;
  out[2] = v3;
  out[3] = v1;
  out[4] = v3;
  out[5] = v2;
  out[6] = std::min(v1, v3);
  out[7] = v1;
  out[8] = std::min(v2, v3);
  out[9] = v2;
  out[10] = v3;
  out[11] = std::min(v1, v2);
}

namespace {

template <typename T>
struct SdfSixDelays {
  T v1;
  T v2;
  T v3;
  T v4;
  T v5;
  T v6;
};

}  // namespace

template <typename T>
static void ExpandSdfDelaysSixDirect(std::vector<T>& out,
                                     const SdfSixDelays<T>& d) {
  out[0] = d.v1;
  out[1] = d.v2;
  out[2] = d.v3;
  out[3] = d.v4;
  out[4] = d.v5;
  out[5] = d.v6;
}

template <typename T>
static void ExpandSdfDelaysSixDerived(std::vector<T>& out,
                                      const SdfSixDelays<T>& d) {
  out[6] = std::min(d.v1, d.v3);
  out[7] = std::max(d.v1, d.v4);
  out[8] = std::min(d.v2, d.v5);
  out[9] = std::max(d.v2, d.v6);
  out[10] = std::max(d.v3, d.v5);
  out[11] = std::min(d.v4, d.v6);
}

template <typename T>
static void ExpandSdfDelaysSix(std::vector<T>& out, const SdfSixDelays<T>& d) {
  ExpandSdfDelaysSixDirect(out, d);
  ExpandSdfDelaysSixDerived(out, d);
}

template <typename T>
static std::vector<T> ExpandListedDelays(const std::vector<T>& v) {
  std::vector<T> out(12, 0);
  if (v.empty()) return out;
  const std::size_t kN = v.size();
  if (kN == 2) {
    ExpandSdfDelaysTwo(out, v[0], v[1]);
  } else if (kN == 3) {
    ExpandSdfDelaysThree(out, v[0], v[1], v[2]);
  } else if (kN == 6) {
    ExpandSdfDelaysSix(out,
                       SdfSixDelays<T>{v[0], v[1], v[2], v[3], v[4], v[5]});
  } else if (kN == 12) {
    std::copy(v.begin(), v.end(), out.begin());
  } else {
    std::fill(out.begin(), out.end(), v[0]);
  }
  return out;
}

template <typename T>
static std::vector<T> ExpandSdfDelaysBy(const std::vector<SdfDelayValue>& vals,
                                        SdfMtm mtm,
                                        T (*select)(const SdfDelayValue&,
                                                    SdfMtm)) {
  std::vector<T> listed;
  listed.reserve(vals.size());
  for (const SdfDelayValue& dv : vals) listed.push_back(select(dv, mtm));
  return ExpandListedDelays(listed);
}

static std::array<bool, 12> HeldTransitions(const std::vector<bool>& written) {
  std::vector<uint8_t> written_flags;
  std::vector<uint8_t> empty_flags;
  written_flags.reserve(written.size());
  empty_flags.reserve(written.size());
  for (const bool kWritten : written) {
    written_flags.push_back(kWritten ? 1 : 0);
    empty_flags.push_back(kWritten ? 0 : 1);
  }
  const std::vector<uint8_t> kWrittenSpread = ExpandListedDelays(written_flags);
  const std::vector<uint8_t> kEmptySpread = ExpandListedDelays(empty_flags);
  std::array<bool, 12> held{};
  for (std::size_t i = 0; i < 12 && !written.empty(); ++i) {
    held[i] = kWrittenSpread[i] == 0 || kEmptySpread[i] == 1;
  }
  return held;
}

static std::vector<bool> ValuesWritten(const std::vector<SdfDelayValue>& values,
                                       SdfMtm mtm) {
  std::vector<bool> written;
  written.reserve(values.size());
  for (const SdfDelayValue& dv : values) {
    written.push_back(!SdfValueHeld(dv, mtm));
  }
  return written;
}

std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm) {
  return ExpandSdfDelaysBy<uint64_t>(vals, mtm, SelectMtm);
}

static std::vector<int64_t> ExpandSignedSdfDelays(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm) {
  return ExpandSdfDelaysBy<int64_t>(vals, mtm, SelectSignedMtm);
}

std::array<uint64_t, 4> ReduceSdfDelaysToThree(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm) {
  std::array<uint64_t, 4> out{0, 0, 0, 0};
  if (vals.empty()) return out;

  out[0] = SelectMtm(vals[0], mtm);
  out[1] = vals.size() >= 2 ? SelectMtm(vals[1], mtm) : out[0];
  out[2] =
      vals.size() >= 3 ? SelectMtm(vals[2], mtm) : std::min(out[0], out[1]);

  out[3] = std::min({out[0], out[1], out[2]});
  return out;
}

namespace {

std::vector<SdfDelayValue> SdfIopathDelayValues(const SdfIopath& io) {
  if (!io.values.empty()) return io.values;
  return {io.rise, io.fall, io.turnoff};
}

void FillSdfIopathDelays(PathDelay& pd, const SdfIopath& io, SdfMtm mtm) {
  const auto kExpanded = ExpandSdfDelays(SdfIopathDelayValues(io), mtm);
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) pd.delays[i] = kExpanded[i];
}

SdfPathDelayIncrement SdfIopathIncrementOf(const SdfIopath& io, SdfMtm mtm) {
  const auto kExpanded = ExpandSignedSdfDelays(SdfIopathDelayValues(io), mtm);
  SdfPathDelayIncrement deltas{};
  for (int i = 0; i < 12; ++i) deltas[i] = kExpanded[i];
  return deltas;
}

PathDelayRetention SdfIopathSimpleRetention(const SdfIopath& io, SdfMtm mtm) {
  PathDelayRetention retain;
  retain.delay = HeldTransitions(ValuesWritten(SdfIopathDelayValues(io), mtm));
  retain.reject = retain.delay;
  retain.error = retain.delay;
  return retain;
}

bool AnnotateSdfIopathSimple(PathDelay& pd, const SdfIopath& io,
                             SpecifyManager& mgr, SdfMtm mtm) {
  const PathDelayRetention kHeld = SdfIopathSimpleRetention(io, mtm);
  if (io.is_increment) {
    SdfPathDelayIncrement deltas = SdfIopathIncrementOf(io, mtm);
    for (std::size_t i = 0; i < 12; ++i) {
      if (kHeld.delay[i]) deltas[i] = 0;
    }
    return mgr.IncrementSdfPathDelay(pd, deltas);
  }
  ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                         mgr.ErrorPulseLimitPercent());
  return mgr.AnnotateSdfPathDelay(pd, kHeld);
}

std::vector<SdfDelayValue> DirectionMember(
    const std::vector<SdfIopathDirection>& directions,
    SdfDelayValue SdfIopathDirection::* member) {
  std::vector<SdfDelayValue> out;
  out.reserve(directions.size());
  for (const SdfIopathDirection& dir : directions) out.push_back(dir.*member);
  return out;
}

std::vector<bool> DirectionWrote(
    const std::vector<SdfIopathDirection>& directions,
    SdfDelayValue SdfIopathDirection::* member,
    bool SdfIopathDirection::* written, SdfMtm mtm) {
  std::vector<bool> out;
  out.reserve(directions.size());
  for (const SdfIopathDirection& dir : directions) {
    out.push_back(dir.*written && !SdfValueHeld(dir.*member, mtm));
  }
  return out;
}

PathDelayRetention DirectionsRetention(
    const std::vector<SdfIopathDirection>& directions, SdfMtm mtm) {
  PathDelayRetention retain;
  retain.delay =
      HeldTransitions(DirectionWrote(directions, &SdfIopathDirection::delay,
                                     &SdfIopathDirection::delay_present, mtm));
  retain.reject =
      HeldTransitions(DirectionWrote(directions, &SdfIopathDirection::reject,
                                     &SdfIopathDirection::reject_present, mtm));
  retain.error =
      HeldTransitions(DirectionWrote(directions, &SdfIopathDirection::error,
                                     &SdfIopathDirection::error_present, mtm));
  return retain;
}

bool AnnotateSdfIopathExtended(PathDelay& pd, const SdfIopath& io,
                               SpecifyManager& mgr, SdfMtm mtm) {
  ApplyGlobalPulseLimits(pd, mgr.RejectPulseLimitPercent(),
                         mgr.ErrorPulseLimitPercent());
  const std::vector<uint64_t> kRejects = ExpandSdfDelays(
      DirectionMember(io.directions, &SdfIopathDirection::reject), mtm);
  const std::vector<uint64_t> kErrors = ExpandSdfDelays(
      DirectionMember(io.directions, &SdfIopathDirection::error), mtm);
  for (std::size_t i = 0; i < 12; ++i) {
    pd.reject_limit[i] = kRejects[i];
    pd.error_limit[i] = kErrors[i];
  }
  return mgr.AnnotateSdfPathDelay(pd, DirectionsRetention(io.directions, mtm));
}

SdfPathDelayIncrement SdfIopathMemberIncrement(
    const std::vector<SdfDelayValue>& listed, const std::array<bool, 12>& held,
    SdfMtm mtm) {
  const std::vector<int64_t> kExpanded = ExpandSignedSdfDelays(listed, mtm);
  SdfPathDelayIncrement deltas{};
  for (std::size_t i = 0; i < 12; ++i) deltas[i] = held[i] ? 0 : kExpanded[i];
  return deltas;
}

bool AnnotateSdfIopathIncrementExtended(const PathDelay& pd,
                                        const SdfIopath& io,
                                        SpecifyManager& mgr, SdfMtm mtm) {
  const PathDelayRetention kHeld = DirectionsRetention(io.directions, mtm);
  const bool kPlaced = mgr.IncrementSdfPathDelay(
      pd, SdfIopathMemberIncrement(SdfIopathDelayValues(io), kHeld.delay, mtm));
  mgr.IncrementSdfPulseLimit(
      pd.src_port, pd.dst_port,
      {SdfIopathMemberIncrement(
           DirectionMember(io.directions, &SdfIopathDirection::reject),
           kHeld.reject, mtm),
       SdfIopathMemberIncrement(
           DirectionMember(io.directions, &SdfIopathDirection::error),
           kHeld.error, mtm)},
      pd.inst_prefix);
  return kPlaced;
}

}  // namespace

void SplitSdfPortSelect(const std::string& port, std::string& name,
                        std::string& select) {
  const size_t kOpen = port.find('[');
  if (kOpen == std::string::npos || kOpen == 0 || port.back() != ']') {
    name = port;
    select.clear();
    return;
  }
  name = port.substr(0, kOpen);
  select = port.substr(kOpen);
}

void AnnotateSdfIopathEntry(const SdfIopath& io, std::string_view inst_prefix,
                            SpecifyManager& mgr, SdfMtm mtm,
                            SdfAnnotationResult& result) {
  PathDelay pd;
  SplitSdfPortSelect(io.src_port, pd.src_port, pd.src_select);
  SplitSdfPortSelect(io.dst_port, pd.dst_port, pd.dst_select);
  pd.inst_prefix = inst_prefix;
  pd.edge = io.src_edge;

  pd.condition = io.condition;
  pd.is_ifnone = io.is_ifnone;

  FillSdfIopathDelays(pd, io, mtm);
  bool placed = false;
  if (!io.extended_form) {
    placed = AnnotateSdfIopathSimple(pd, io, mgr, mtm);
  } else if (io.is_increment) {
    placed = AnnotateSdfIopathIncrementExtended(pd, io, mgr, mtm);
  } else {
    placed = AnnotateSdfIopathExtended(pd, io, mgr, mtm);
  }
  if (placed) return;
  result.warnings.push_back(
      "SDF annotator: unable to annotate IOPATH delay from " + io.src_port +
      " to " + io.dst_port);
}

namespace {

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

bool SdfVersionHasNetdelay(std::string_view version) {
  if (version.empty()) return true;
  for (std::string_view known : {"1.0", "2.0", "2.1", "4.0"}) {
    if (version.find(known) != std::string_view::npos) return true;
  }
  return false;
}

std::vector<SdfDelayValue> SdfInterconnectDelayValues(
    const SdfInterconnect& ic) {
  if (!ic.values.empty()) return ic.values;
  return {ic.rise, ic.fall};
}

}  // namespace

static std::string PortUnderCell(std::string_view inst_prefix,
                                 const std::string& port) {
  if (port.empty()) return port;
  return std::string(inst_prefix) + port;
}

void AnnotateSdfInterconnectEntry(const SdfInterconnect& ic,
                                  const SdfCellSource& src, SpecifyManager& mgr,
                                  SdfMtm mtm, SdfAnnotationResult& result) {
  if (ic.kind == SdfInterconnectKind::kNetdelay &&
      !SdfVersionHasNetdelay(src.file.version)) {
    result.warnings.push_back(
        "SDF annotator: unable to annotate NETDELAY construct, which SDF "
        "version " +
        src.file.version + " does not define");
    return;
  }

  SdfInterconnectAnnotation ann;
  ann.source = PortUnderCell(src.inst_prefix, ic.src_port);
  ann.load = PortUnderCell(src.inst_prefix, ic.dst_port);
  ann.construct = SdfInterconnectConstructOf(ic.kind);
  ann.is_increment = ic.is_increment;

  const auto kExpanded = ExpandSdfDelays(SdfInterconnectDelayValues(ic), mtm);
  for (int i = 0; i < 12; ++i) ann.delays[i] = kExpanded[i];
  if (!ic.directions.empty()) {
    ann.held = DirectionsRetention(ic.directions, mtm);
    ann.limits_written =
        std::ranges::any_of(ic.directions, [](const SdfIopathDirection& dir) {
          return dir.reject_present || dir.error_present;
        });
    const auto kRejects = ExpandSdfDelays(
        DirectionMember(ic.directions, &SdfIopathDirection::reject), mtm);
    const auto kErrors = ExpandSdfDelays(
        DirectionMember(ic.directions, &SdfIopathDirection::error), mtm);
    for (std::size_t i = 0; i < 12; ++i) {
      ann.reject_limit[i] = kRejects[i];
      ann.error_limit[i] = kErrors[i];
    }
  }

  SdfInterconnectOutcome outcome = mgr.AnnotateSdfInterconnect(ann);
  if (outcome.annotated && ic.kind != SdfInterconnectKind::kNetdelay) {
    GetGlobalVpiContext().PlaceSdfDelayDevice(ann.source, ann.load);
  }
  for (auto& warning : outcome.warnings) {
    result.warnings.push_back(std::move(warning));
  }
  if (!outcome.annotated && outcome.warnings.empty()) {
    result.warnings.push_back("SDF annotator: unable to annotate " +
                              std::string(SdfInterconnectKeyword(ic.kind)) +
                              " delay on " + ic.dst_port);
  }
}

namespace {

std::vector<SdfDelayValue> SdfDeviceDelayValues(const SdfDevice& dev) {
  if (!dev.values.empty()) return dev.values;
  return {dev.rise, dev.fall, dev.turnoff};
}

}  // namespace

static std::array<bool, 4> DeviceThreeStateHeld(
    const std::vector<SdfDelayValue>& values, SdfMtm mtm) {
  std::array<bool, 4> held{};
  if (values.empty()) return held;
  const bool kRise = !SdfValueHeld(values[0], mtm);
  const bool kFall = values.size() >= 2 ? !SdfValueHeld(values[1], mtm) : kRise;
  const bool kOff =
      values.size() >= 3 ? !SdfValueHeld(values[2], mtm) : kRise && kFall;
  held = {!kRise, !kFall, !kOff, !(kRise && kFall && kOff)};
  return held;
}

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
  ann.three_state_held = DeviceThreeStateHeld(kValues, mtm);
  ann.held = HeldTransitions(ValuesWritten(kValues, mtm));

  if (mgr.AnnotateSdfDeviceDelay(ann, inst_prefix)) return;
  const std::string kTarget = dev.port_instance.empty()
                                  ? std::string("module outputs")
                                  : dev.port_instance;
  result.warnings.push_back(
      "SDF annotator: unable to annotate DEVICE delay on " + kTarget);
}

namespace {

int64_t SdfPulseLimitValue(const SdfDelayValue& dv, SdfMtm mtm,
                           bool is_increment) {
  if (is_increment) return SelectSignedMtm(dv, mtm);
  return static_cast<int64_t>(SelectMtm(dv, mtm));
}

}  // namespace

void AnnotateSdfPulseLimitEntry(const SdfPulseLimit& pl,
                                std::string_view inst_prefix,
                                SpecifyManager& mgr, SdfMtm mtm,
                                SdfAnnotationResult& result) {
  const bool kPlaced = mgr.AddSdfPulseLimit(
      SdfPulseLimitSpec{
          pl.src_port,
          pl.dst_port,
          SdfPulseLimitValue(pl.reject, mtm, pl.is_increment),
          SdfPulseLimitValue(pl.error, mtm, pl.is_increment),
          pl.has_error,
          pl.is_percent,
          pl.is_increment,
      },
      inst_prefix);
  if (kPlaced) return;
  result.warnings.push_back(std::string("SDF annotator: unable to annotate ") +
                            (pl.is_percent ? "PATHPULSEPERCENT" : "PATHPULSE") +
                            " limits from " + pl.src_port + " to " +
                            pl.dst_port);
}

void AnnotateSdfSpecparamEntry(const SdfSpecparam& sp,
                               std::string_view inst_prefix,
                               SpecifyManager& mgr, SdfMtm mtm,
                               SdfAnnotationResult& result) {
  if (!mgr.KnowsSpecparam(inst_prefix, sp.name)) {
    result.warnings.push_back("SDF annotator: unable to annotate LABEL " +
                              sp.name + ", which names no specparam");
    return;
  }
  SpecparamValue value;
  value.name = sp.name;
  value.value = SelectMtm(sp.value, mtm);
  value.real_value = SelectRealMtm(sp.value, mtm);

  if (sp.is_increment) {
    mgr.IncrementSpecparamValue(std::move(value), inst_prefix);
  } else {
    mgr.SetSpecparamValue(std::move(value), inst_prefix);
  }
}

}  // namespace delta
