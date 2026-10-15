// §32.4.2's TIMINGCHECK constructs: Table 32-2's mapping of each SDF timing
// check onto the SystemVerilog checks it annotates, and the hand-over of one
// entry to the SpecifyManager. AnnotateSdfCellEntry
// (simulator/sdf_annotate.cpp) is the caller.

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/sdf_annotate_internal.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"

namespace delta {

namespace {

// Mirrors the `push` lambda in ExpandSdfTimingCheckTargets: appends a new
// annotation seeded from the timing check and returns a reference to it.
SdfTcAnnotation& PushSdfTcAnnotation(std::vector<SdfTcAnnotation>& targets,
                                     const SdfTimingCheck& tc,
                                     TimingCheckKind kind) {
  SdfTcAnnotation a;
  a.kind = kind;
  SplitSdfPortSelect(tc.ref_port, a.ref_signal, a.ref_select);
  a.ref_edge = tc.ref_edge;
  a.ref_edge_descriptors = tc.ref_edge_descriptors;
  SplitSdfPortSelect(tc.data_port, a.data_signal, a.data_select);
  a.data_edge = tc.data_edge;
  a.data_edge_descriptors = tc.data_edge_descriptors;
  a.condition = tc.condition;
  a.ref_condition = tc.ref_condition;
  a.data_condition = tc.data_condition;
  targets.push_back(std::move(a));
  return targets.back();
}

// One value of an SDF timing check: what it selects, and whether the file
// wrote it at all rather than as empty parentheses.
struct SdfTcValue {
  int64_t value = 0;
  bool written = true;
};

// §32.5: a field the entry wrote a value for takes it; one it wrote as empty
// parentheses is held at what the check already carries, so the field is left
// unset.
template <typename F>
void SetFromSdf(bool& set, F& field, SdfTcValue v) {
  if (!v.written) return;
  set = true;
  field = static_cast<F>(v.value);
}

void PopulateSdfTcSetupHold(std::vector<SdfTcAnnotation>& targets,
                            const SdfTimingCheck& tc, SdfCheckType check_type,
                            SdfTcValue v1, SdfTcValue v2) {
  switch (check_type) {
    case SdfCheckType::kSetup: {
      auto& s = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetup);
      SetFromSdf(s.set_limit, s.limit, v1);
      auto& sh = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetuphold);
      SetFromSdf(sh.set_limit, sh.limit, v1);
      break;
    }
    case SdfCheckType::kHold: {
      auto& h = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kHold);
      SetFromSdf(h.set_limit, h.limit, v1);
      auto& sh = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetuphold);
      SetFromSdf(sh.set_limit2, sh.limit2, v1);
      break;
    }
    case SdfCheckType::kSetuphold: {
      auto& s = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetup);
      SetFromSdf(s.set_limit, s.limit, v1);
      auto& h = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kHold);
      SetFromSdf(h.set_limit, h.limit, v2);
      auto& sh = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSetuphold);
      SetFromSdf(sh.set_limit, sh.limit, v1);
      SetFromSdf(sh.set_limit2, sh.limit2, v2);
      break;
    }
    default:
      break;
  }
}

void PopulateSdfTcRecRem(std::vector<SdfTcAnnotation>& targets,
                         const SdfTimingCheck& tc, SdfCheckType check_type,
                         SdfTcValue v1, SdfTcValue v2) {
  switch (check_type) {
    case SdfCheckType::kRecovery: {
      auto& r = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecovery);
      SetFromSdf(r.set_limit, r.limit, v1);
      auto& rr = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecrem);
      SetFromSdf(rr.set_limit, rr.limit, v1);
      break;
    }
    case SdfCheckType::kRemoval: {
      auto& r = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRemoval);
      SetFromSdf(r.set_limit, r.limit, v1);
      auto& rr = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecrem);
      SetFromSdf(rr.set_limit2, rr.limit2, v1);
      break;
    }
    case SdfCheckType::kRecrem: {
      auto& r = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecovery);
      SetFromSdf(r.set_limit, r.limit, v1);
      auto& rm = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRemoval);
      SetFromSdf(rm.set_limit, rm.limit, v2);
      auto& rr = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kRecrem);
      SetFromSdf(rr.set_limit, rr.limit, v1);
      SetFromSdf(rr.set_limit2, rr.limit2, v2);
      break;
    }
    default:
      break;
  }
}

void PopulateSdfTcSkewWidthPeriod(std::vector<SdfTcAnnotation>& targets,
                                  const SdfTimingCheck& tc,
                                  SdfCheckType check_type, SdfTcValue v1,
                                  SdfTcValue v2) {
  switch (check_type) {
    case SdfCheckType::kSkew: {
      auto& s = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kSkew);
      SetFromSdf(s.set_limit, s.limit, v1);
      auto& ts = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kTimeskew);
      SetFromSdf(ts.set_limit, ts.limit, v1);
      break;
    }
    case SdfCheckType::kBidirectskew: {
      auto& fs = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kFullskew);
      SetFromSdf(fs.set_limit, fs.limit, v1);
      SetFromSdf(fs.set_limit2, fs.limit2, v2);
      break;
    }
    case SdfCheckType::kWidth: {
      auto& w = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kWidth);
      SetFromSdf(w.set_limit, w.limit, v1);
      break;
    }
    case SdfCheckType::kPeriod: {
      auto& p = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kPeriod);
      SetFromSdf(p.set_limit, p.limit, v1);
      break;
    }
    case SdfCheckType::kNochange: {
      auto& nc = PushSdfTcAnnotation(targets, tc, TimingCheckKind::kNochange);
      SetFromSdf(nc.set_start_edge_offset, nc.start_edge_offset, v1);
      SetFromSdf(nc.set_end_edge_offset, nc.end_edge_offset, v2);
      break;
    }
    default:
      break;
  }
}

}  // namespace

static std::vector<SdfTcAnnotation> ExpandSdfTimingCheckTargets(
    const SdfTimingCheck& tc, SdfMtm mtm) {
  const SdfTcValue kV1{SelectSignedMtm(tc.limit, mtm),
                       !SdfValueHeld(tc.limit, mtm)};
  const SdfTcValue kV2{SelectSignedMtm(tc.limit2, mtm),
                       !SdfValueHeld(tc.limit2, mtm)};
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

namespace {

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

}  // namespace

// §32.4.2 Table 32-2: hand one TIMINGCHECK entry to the manager, which updates
// whichever declared checks it matches.
//
// §31.2 puts a system timing check inside a specify block and §30.3 puts that
// block inside a module declaration, so two instances of one cell declare
// checks naming identically spelled signals. `inst_prefix` is what
// SdfCellPrefixInRegion made of the cell's CELLINSTANCE, and it travels beside
// the annotation rather than on it because SdfTcAnnotation
// (simulator/specify_sdf.h) has no field for it, as with AnnotateSdfDeviceEntry
// above. It is what holds the constraint to the checks of the one instance the
// entry names.
void AnnotateSdfTimingCheckEntry(const SdfTimingCheck& tc,
                                 std::string_view inst_prefix,
                                 SpecifyManager& mgr, SdfMtm mtm,
                                 SdfAnnotationResult& result) {
  // §32.3: an SCOND or CCOND conditions the check in a way no declared check's
  // condition can be matched against, so the entry is data the annotator
  // cannot place.
  if (!tc.trailing_construct.empty()) {
    result.warnings.push_back("SDF annotator: unable to annotate " +
                              std::string(SdfCheckTypeName(tc.check_type)) +
                              " timing check on " + tc.ref_port + "/" +
                              tc.data_port + " carrying " +
                              tc.trailing_construct);
    return;
  }
  // An SDF check offers several candidate annotations so it can update
  // whichever form the specify block happens to declare; landing any one of
  // them means the constraint was placed.
  bool placed = false;
  for (const auto& target : ExpandSdfTimingCheckTargets(tc, mtm)) {
    if (mgr.AnnotateSdfTimingCheck(target, inst_prefix, result.warnings)) {
      placed = true;
    }
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

}  // namespace delta
