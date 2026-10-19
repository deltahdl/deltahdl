// One SDF construct onto the SystemVerilog structure it annotates, once for
// each kind of entry a CELL can carry: DEVICE and IOPATH from §32.4.1
// Table 32-1, LABEL from §32.4.3, INTERCONNECT, PORT and NETDELAY from §32.4.4
// Table 32-3, PATHPULSE and PATHPULSEPERCENT from §32.7, and the checks a
// TIMINGCHECK section lists. AnnotateSdfDeviceEntry, AnnotateSdfIopathEntry,
// AnnotateSdfSpecparamEntry, AnnotateSdfInterconnectEntry,
// AnnotateSdfPulseLimitEntry and AnnotateSdfTimingCheckEntry are those six,
// the last of them in simulator/sdf_annotate_timing_check.cpp.
// Each takes one entry's values to the SpecifyManager call that places them.
// Where the design has nothing an INTERCONNECT, a DEVICE or a timing check can
// reach, §32.3 has the entry warned about rather than dropped in silence; a
// delay or a specparam that matches nothing is simply recorded.
//
// §32.8 Table 32-4 stands here as well, in ExpandSdfDelays and
// ReduceSdfDelaysToThree, which simulator/sdf_parser.h declares: they spread
// the delay values an entry listed over the state transitions its target
// carries, and every one of the six reads its delays through them.
//
// simulator/sdf_annotate.cpp holds the rest of the annotator -- which cells an
// $sdf_annotate call reaches (§32.9) and the order one cell's constructs are
// applied in (§32.5). AnnotateSdfCellEntry there is the only caller of the six.

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
int64_t SelectSignedMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  const auto kMagnitude = static_cast<int64_t>(SelectMtmMagnitude(dv, mtm));
  return SelectMtmNegative(dv, mtm) ? -kMagnitude : kMagnitude;
}

// The selected member exactly as written, its fraction and its sign included.
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

// The selected value as the unsigned quantity the annotator's other targets
// hold -- a propagation delay, a timing constraint limit, a specparam value.
// None of those can carry a negative number, and §30.5.1 puts a delay whose
// expression is negative at zero, so that is where a value written negative
// reads here.
uint64_t SelectMtm(const SdfDelayValue& dv, SdfMtm mtm) {
  if (SelectMtmNegative(dv, mtm)) return 0;
  return SelectMtmMagnitude(dv, mtm);
}

// §32.8 Table 32-4's spreading of one, two, three, six or twelve listed values
// over the twelve transitions, for a value of type T: the delay an entry
// states, or, for an INCREMENT, the signed amount it adds (§32.7).
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

// The six explicit SDF delay-transition values supplied for the 6-tuple delay
// form (IEEE 1800 SDF annotation): 0->1, 1->0, 0->Z, Z->1, 1->Z, Z->0. They
// together describe one domain object - a single delay specification - so they
// travel as one struct rather than six loose scalars.
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

// The twelve transition values the listed values `v` spread to.
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

// The twelve transition values `vals` spreads to, each listed value read by
// `select`, which decides what a value written negative becomes.
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

// §32.5 with §32.8: the transitions an entry leaves as they stood, where
// `written` says which of its listed values it wrote and which it left as
// empty parentheses. A transition Table 32-4 takes from one listed value is
// held where that value is empty, and one it takes as the smaller or the
// larger of two where either is: spread, the written flags say a smaller-of
// slot is written only where both are, and the empty flags say a larger-of
// slot is empty where either is.
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

// Which of the listed values provide one for `mtm` to select (SdfValueHeld).
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

// §32.7 (printed pages 930-931): an INCREMENT entry's twelve transition
// amounts, each with the sign the file wrote, since a negative value in
// INCREMENT mode lowers what it is added to.
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
  // §28.16's Table 28-9: of two delays, the smaller is the turn-off delay.
  out[2] =
      vals.size() >= 3 ? SelectMtm(vals[2], mtm) : std::min(out[0], out[1]);

  out[3] = std::min({out[0], out[1], out[2]});
  return out;
}

namespace {

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

// §32.7: the twelve amounts an INCREMENT IOPATH adds, signed.
SdfPathDelayIncrement SdfIopathIncrementOf(const SdfIopath& io, SdfMtm mtm) {
  const auto kExpanded = ExpandSignedSdfDelays(SdfIopathDelayValues(io), mtm);
  SdfPathDelayIncrement deltas{};
  for (int i = 0; i < 12; ++i) deltas[i] = kExpanded[i];
  return deltas;
}

// §32.5 with §32.8: the transitions a simple iopath leaves as they stood,
// those Table 32-4 takes from a value written as empty parentheses. Nothing is
// written for such a transition, its pulse limits included.
PathDelayRetention SdfIopathSimpleRetention(const SdfIopath& io, SdfMtm mtm) {
  PathDelayRetention retain;
  retain.delay = HeldTransitions(ValuesWritten(SdfIopathDelayValues(io), mtm));
  retain.reject = retain.delay;
  retain.error = retain.delay;
  return retain;
}

// Handles the non-extended (legacy) iopath form: increment in place, or apply
// the global pulse limits and add. Answers whether a declared path took it.
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

// One member of every direction an extended iopath wrote: its delay, its
// reject limit or its error limit, an empty one read as zero.
std::vector<SdfDelayValue> DirectionMember(
    const std::vector<SdfIopathDirection>& directions,
    SdfDelayValue SdfIopathDirection::* member) {
  std::vector<SdfDelayValue> out;
  out.reserve(directions.size());
  for (const SdfIopathDirection& dir : directions) out.push_back(dir.*member);
  return out;
}

// Which directions wrote that member, `written` saying whether it was left as
// empty parentheses and SdfValueHeld whether it left out the member `mtm`
// selects.
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

// §32.5 with §32.8: an extended iopath leaves as they stood the delays and the
// limits it wrote as empty parentheses, each transition held or written by the
// directions Table 32-4 takes it from. The delays and the two limits are
// decided apart, so an entry may supply one and hold the others.
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

// Handles the extended iopath form: each direction's reject and error limits
// spread over the transitions as its delays do (§32.8), and those of a
// transition whose directions left them empty, or wrote none, held at their
// current values (§32.5).
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

// §32.7: the twelve amounts an extended iopath in INCREMENT mode adds to one
// of the path's members, spread by §32.8 like its delays. A transition the
// entry held with empty parentheses is one it is not changing, so its amount
// is zero; one written with a leading minus sign lowers what it reaches.
SdfPathDelayIncrement SdfIopathMemberIncrement(
    const std::vector<SdfDelayValue>& listed, const std::array<bool, 12>& held,
    SdfMtm mtm) {
  const std::vector<int64_t> kExpanded = ExpandSignedSdfDelays(listed, mtm);
  SdfPathDelayIncrement deltas{};
  for (std::size_t i = 0; i < 12; ++i) deltas[i] = held[i] ? 0 : kExpanded[i];
  return deltas;
}

// §32.7: an extended iopath in INCREMENT mode modifies what the path already
// carries rather than replacing it, on both halves of the entry. Its delay
// values add to the path's delays and its pulse-limit values to the limits the
// path already holds, transition by transition. Nothing here derives a limit
// from the percentage settings: those supply a limit a construct did not
// state, and an INCREMENT entry states a change to the limit already in place.
//
// The delays go through IncrementSdfPathDelay and the two limits through
// IncrementSdfPulseLimit, and both match PathDelay::inst_prefix, so the whole
// entry reaches the one instance its cell named.
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

// §32.4.1: an IOPATH names its terminals by the cell's own port names, so the
// path it reaches is told from the identically spelled path of another instance
// of the same cell by PathDelay::inst_prefix alone. The prefix the cell's
// CELLINSTANCE gave (SdfCellPrefixInRegion) is stamped on here, which is what
// SpecifyManager::AnnotateSdfPathDelay and IncrementSdfPathDelay match on.
// §32.3: an entry no declared path takes is data the annotator could not
// place, so it is warned about.
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

}  // namespace

// §32.9: an interconnect entry's ports are named within the instance its cell
// names, which `inst_prefix` (SdfCellPrefixInRegion) spells, so they are read
// below it rather than from the top of the design.
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

  // §32.4.4: interconnect delays fill in their twelve transition delays from
  // the values the entry lists exactly the way a specify path delay does,
  // their pulse limits too where the values state them, and §32.5 holds what
  // a value written empty stands for.
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
  // §37.45: an intermodule path delay and a module input port delay are each
  // one a delay device stands for, so the VPI model places one where the entry
  // annotated it. A NETDELAY delays a whole net, none of the three kinds of
  // delay Annex K.2 gives a device.
  if (outcome.annotated && ic.kind != SdfInterconnectKind::kNetdelay) {
    GetGlobalVpiContext().PlaceSdfDelayDevice(ann.source, ann.load);
  }
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

namespace {

// §32.8: the delay values a DEVICE entry listed. A file's entry carries the
// whole list; one assembled in memory rather than parsed carries only its three
// named fields, and is read as the triple those fields spell.
std::vector<SdfDelayValue> SdfDeviceDelayValues(const SdfDevice& dev) {
  if (!dev.values.empty()) return dev.values;
  return {dev.rise, dev.fall, dev.turnoff};
}

}  // namespace

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
// SdfCellPrefixInRegion made of the cell's CELLINSTANCE, and it travels beside
// the entry rather than on it because SdfDeviceAnnotation
// (simulator/specify_sdf.h) has no field for it. It is what holds the delay to
// the outputs of the one instance the entry names.
// §32.5 with §32.8: which of the three delays and the delay to x a DEVICE entry
// leaves as they stood on a primitive -- each one the reduction takes from a
// value written empty, the turn-off delay of two values held where either
// is, and the delay to x, the least of the three, where any of them is.
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

// §32.7: how one of a pulse-limit entry's two values reads. In INCREMENT mode
// it is an amount that may lower a limit, so the sign the file wrote is kept;
// stated outright it names a limit itself, where a sign has no meaning.
int64_t SdfPulseLimitValue(const SdfDelayValue& dv, SdfMtm mtm,
                           bool is_increment) {
  if (is_increment) return SelectSignedMtm(dv, mtm);
  return static_cast<int64_t>(SelectMtm(dv, mtm));
}

}  // namespace

// §32.7: hand over one PATHPULSE or PATHPULSEPERCENT entry, in whichever mode
// the section carrying it was written.
//
// §30.4 names a path's terminals by the module's own port names, so two
// instances of one cell declare paths spelled identically. `inst_prefix` is
// what SdfCellPrefixInRegion worked out for the cell, and it travels beside the
// entry rather than on it because SdfPulseLimitSpec (simulator/specify_sdf.h)
// has no field for it. SpecifyManager::AddSdfPulseLimit matches it against
// PathDelay::inst_prefix, so the limits reach the one instance the entry names.
void AnnotateSdfPulseLimitEntry(const SdfPulseLimit& pl,
                                std::string_view inst_prefix,
                                SpecifyManager& mgr, SdfMtm mtm,
                                SdfAnnotationResult& result) {
  const bool kPlaced = mgr.AddSdfPulseLimit(
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
  // §32.3: limits no declared path between the two ports takes are data the
  // annotator could not place.
  if (kPlaced) return;
  result.warnings.push_back(std::string("SDF annotator: unable to annotate ") +
                            (pl.is_percent ? "PATHPULSEPERCENT" : "PATHPULSE") +
                            " limits from " + pl.src_port + " to " +
                            pl.dst_port);
}

// §32.4.3: hand over one LABEL entry. §30.3 has a specify block declare its
// specparams by bare names, so `inst_prefix` -- SdfCellPrefixInRegion's answer
// for the cell, as for the three siblings above -- holds it to that instance.
void AnnotateSdfSpecparamEntry(const SdfSpecparam& sp,
                               std::string_view inst_prefix,
                               SpecifyManager& mgr, SdfMtm mtm,
                               SdfAnnotationResult& result) {
  // §32.3: a name the instance has no specparam under is data the annotator
  // could not place.
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
