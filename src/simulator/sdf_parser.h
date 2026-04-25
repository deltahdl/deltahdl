#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"

namespace delta {

class SpecifyManager;

// =============================================================================
// SDF data structures (IEEE 1800-2023 §32, IEEE 1497-2001)
// =============================================================================

struct SdfDelayValue {
  uint64_t min_val = 0;
  uint64_t typ_val = 0;
  uint64_t max_val = 0;
};

struct SdfIopath {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfDelayValue turnoff;
  bool is_increment = false;
  // §32.4.1 Table 32-1 row "(COND (IOPATH...)": text of the SDF condition
  // expression (e.g. "mode" for `(COND mode (IOPATH ...))`). Empty means
  // the iopath is nonconditional, which §32.4.1 routes differently from a
  // conditional one. The annotator compares this against the SystemVerilog
  // condition text on PathDelay to find a same-condition match.
  std::string condition;
  // §32.4.1 Table 32-1 row "(CONDELSE (IOPATH...) → ifnone": the CONDELSE
  // wrapper carries no expression — its semantics are exclusively to land
  // on the `ifnone` specify path between the two named ports. Set true by
  // the parser when it sees CONDELSE; mutually exclusive with `condition`
  // being non-empty.
  bool is_ifnone = false;
};

enum class SdfCheckType : uint8_t {
  kSetup,
  kHold,
  kSetuphold,
  kRecovery,
  kRemoval,
  kRecrem,
  kWidth,
  kPeriod,
  kSkew,
  // §32.4.2 Table 32-2 row "(BIDIRECTSKEW v1 v2... → $fullskew(v1,v2)":
  // SDF's BIDIRECTSKEW has no direct same-named SystemVerilog timing
  // check; it expands to $fullskew during annotation.
  kBidirectskew,
  kNochange,
};

struct SdfTimingCheck {
  SdfCheckType check_type = SdfCheckType::kSetup;
  std::string ref_port;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_port;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  // limit2 carries v2 for the §32.4.2 Table 32-2 two-value kinds:
  // SETUPHOLD, RECREM, BIDIRECTSKEW, NOCHANGE. Defaulted otherwise.
  SdfDelayValue limit;
  SdfDelayValue limit2;
  // §32.4.2 paragraph 2: textual condition associated with the reference
  // signal of the SDF timing check (the SDF analogue of SystemVerilog's
  // `&&&` scalar timing check condition). Empty when the SDF check
  // declares no condition; an empty value triggers the LRM's
  // "shall match all corresponding SystemVerilog timing checks
  // regardless of whether conditions are present" rule, while a
  // non-empty value forces an exact match against the SystemVerilog
  // timing check's stored `condition` text.
  std::string condition;
};

// §32.2: SDF specparam value update. Carries the new value the SDF file
// supplies for a SystemVerilog specparam. The detailed mapping from SDF's
// LABEL section to this struct is §32.4's responsibility; the §32.2
// contract is just that backannotation can carry such a value through.
struct SdfSpecparam {
  std::string name;
  SdfDelayValue value;
};

// §32.2: SDF interconnect delay between two ports. Same split: §32.4 owns
// the INTERCONNECT/PORT parsing, §32.2 owns the fact that backannotation
// names interconnect delays as one of its four update categories.
struct SdfInterconnect {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
};

// §32.4.1 Table 32-1 PATHPULSE / PATHPULSEPERCENT rows: an SDF entry that
// updates the per-path pulse-filter limits between two ports. The
// `is_percent` flag distinguishes the two table rows — absolute reject /
// error values when false, percentages of the matched PathDelay when
// true. `has_error` carries the LRM rule that a single-value entry
// collapses the X band to zero by mirroring reject into error.
struct SdfPulseLimit {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue reject;
  SdfDelayValue error;
  bool has_error = false;
  bool is_percent = false;
};

struct SdfCell {
  std::string cell_type;
  std::string instance;
  std::vector<SdfIopath> iopaths;
  std::vector<SdfTimingCheck> timing_checks;
  // §32.2's two remaining backannotation categories. Empty by default so
  // existing IOPATH/TIMINGCHECK-only flows keep observing zero specparams
  // and zero interconnects.
  std::vector<SdfSpecparam> specparams;
  std::vector<SdfInterconnect> interconnects;
  // §32.4.1 Table 32-1 PATHPULSE / PATHPULSEPERCENT entries collected from
  // the cell's DELAY section.
  std::vector<SdfPulseLimit> pulse_limits;
};

struct SdfFile {
  std::string version;
  std::string design;
  std::vector<SdfCell> cells;
  // §32.3: SDF data the parser recognised as residing inside one of the
  // four §32.2 backannotation categories (i.e. clearly related to
  // SystemVerilog timing) but that it could not turn into one of the
  // typed entries above. Each string is a short label naming the
  // construct (e.g. "COND", "PATHPULSE"). The annotator surfaces one
  // warning per entry. Constructs unrelated to SystemVerilog timing are
  // not recorded here so they remain silent under §32.3's ignore rule.
  std::vector<std::string> unannotatable;
};

// Min/typ/max selection mode (§32.9).
enum class SdfMtm : uint8_t {
  kMinimum,
  kTypical,
  kMaximum,
};

// =============================================================================
// SDF parser
// =============================================================================

// Parse an SDF string into an SdfFile structure.
bool ParseSdf(std::string_view input, SdfFile& out);

// =============================================================================
// Delay expansion (Table 32-4)
// =============================================================================

// Expand 1/2/3/6/12 delay values into 12 transition delays.
std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm);

// =============================================================================
// SDF annotation
// =============================================================================

// §32.3: outcome of a single backannotation pass. `warnings` carries one
// human-readable string per piece of SDF data the annotator was unable
// to apply, satisfying the LRM rule that the annotator "shall issue a
// warning for any data it is unable to annotate." Constructs the
// annotator deliberately ignored under the same clause's
// "unrelated to SystemVerilog timing" rule are not represented here.
struct SdfAnnotationResult {
  std::vector<std::string> warnings;
};

// Apply parsed SDF data to a SpecifyManager.
SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm);

}  // namespace delta
