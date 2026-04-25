#pragma once

#include <array>
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
  // §32.5 examples 2 and 3: the SDF grammar admits an extended IOPATH
  // shape `((delay) (reject) (error))` per direction, where any of the
  // three inner groups may be empty parens to "hold the current values
  // of the pulse limits". The simple form `(delay) (delay)` leaves
  // `extended_form` false; the parser flips it true when it sees the
  // nested triplet, and the *_present flags below distinguish supplied
  // values from the LRM's empty-parens "preserve" marker. The annotator
  // routes the extended form through a preservation-aware code path so
  // a prior PATHPULSE survives an IOPATH with empty pulse-limit slots.
  bool extended_form = false;
  bool rise_delay_present = true;
  bool fall_delay_present = true;
  SdfDelayValue rise_reject;
  bool rise_reject_present = false;
  SdfDelayValue rise_error;
  bool rise_error_present = false;
  SdfDelayValue fall_reject;
  bool fall_reject_present = false;
  SdfDelayValue fall_error;
  bool fall_error_present = false;
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
//
// §32.6 sentence 3: a specparam parsed inside (LABEL (INCREMENT ...))
// carries the modify-vs-overwrite bit forward so the annotator can
// route the entry through the additive specparam path instead of the
// overwriting one when accumulating across SDF files.
struct SdfSpecparam {
  std::string name;
  SdfDelayValue value;
  bool is_increment = false;
};

// §32.4.4 Table 32-3: which of the three SDF construct shapes produced
// this interconnect entry. INTERCONNECT names a source/load pair;
// PORT and NETDELAY name only the load and represent the delay from all
// sources on the net to that load. The kind survives onto InterconnectDelay
// so a future stage can apply the form-specific rules (NETDELAY's input/
// inout-only restriction, PORT's fan-out from all sources, INTERCONNECT's
// source-port direction and same-net validation).
enum class SdfInterconnectKind : uint8_t {
  kInterconnect,
  kPort,
  kNetdelay,
};

// §32.2: SDF interconnect delay between two ports. Same split: §32.4 owns
// the INTERCONNECT/PORT parsing, §32.2 owns the fact that backannotation
// names interconnect delays as one of its four update categories.
//
// §32.4.4: PORT and NETDELAY entries leave src_port empty — the LRM's
// "delay from all sources" semantics are encoded by the absence of a
// named source rather than a synthetic placeholder. The `kind` field
// distinguishes them from INTERCONNECT for downstream rules.
//
// §32.6 sentence 3: an interconnect entry parsed inside (DELAY (INCREMENT
// ...)) carries the INCREMENT-vs-ABSOLUTE bit forward so the annotator
// can route the entry through the modify (additive) path instead of the
// overwrite path when accumulating across SDF files.
struct SdfInterconnect {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfInterconnectKind kind = SdfInterconnectKind::kInterconnect;
  bool is_increment = false;
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

// §32.5 sentence 1: "SDF annotation is an ordered process. The constructs
// from the SDF file are annotated in their order of occurrence." Within a
// DELAY section the parser may interleave IOPATH, PATHPULSE, INTERCONNECT,
// PORT, and NETDELAY entries, and the LRM examples on page 929-930 hinge
// on those entries being applied in the order they appear (a PATHPULSE
// followed by an IOPATH overwrites the former, an INTERCONNECT followed
// by a PORT is overwritten by the latter, and so on). The category
// vectors below preserve the parsed entries by kind so existing readers
// can still inspect them; this companion vector records the source order
// the annotator must walk to satisfy §32.5.
enum class SdfDelayEntryKind : uint8_t {
  kIopath,
  kPulseLimit,
  kInterconnect,
};

struct SdfDelayEntryRef {
  SdfDelayEntryKind kind = SdfDelayEntryKind::kIopath;
  uint32_t index = 0;  // index into the matching cell vector
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
  // §32.5 source-order trail through the DELAY section. Each ref points
  // back into one of `iopaths`, `pulse_limits`, or `interconnects`, in
  // the order the parser saw them. Empty for cells built programmatically
  // by tests; AnnotateSdfToManager falls back to a category-by-category
  // derived order in that case.
  std::vector<SdfDelayEntryRef> delay_entry_order;
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

// §32.9 Table 32-5: keyword strings parsed from the mtm_spec argument
// of $sdf_annotate. The four enumerators correspond to the four rows
// of the table; kToolControl (the LRM default) is distinct from the
// three named values because it defers the actual MTM choice to
// whatever the simulator's own delay-mode option selected, rather
// than naming a slot itself. Resolving the keyword to a concrete
// SdfMtm therefore requires a second piece of information — the
// simulator's current default — which ResolveSdfMtm consumes.
enum class SdfMtmKeyword : uint8_t {
  kMaximum,
  kMinimum,
  kToolControl,
  kTypical,
};

// §32.9 Table 32-6: keyword strings parsed from the scale_type
// argument of $sdf_annotate. The four enumerators correspond to the
// four rows of the table; kFromMtm (the LRM default) applies each
// scale factor to its matching min/typ/max slot independently, while
// the three single-source forms broadcast the named source value
// through all three multipliers.
enum class SdfScaleType : uint8_t {
  kFromMtm,
  kFromMaximum,
  kFromMinimum,
  kFromTypical,
};

// §32.9 scale_factors argument: triplet of multipliers expressed in
// SDF as "min:typ:max" (default "1.0:1.0:1.0"). Each factor scales
// one slot of the SDF triplet selected by scale_type. Stored as
// double because the LRM example "1.6:1.4:1.2" requires fractional
// precision, with the result rounded to integer ticks at the moment
// the scaled value lands back on an SdfDelayValue.
struct SdfScaleFactors {
  double min_factor = 1.0;
  double typ_factor = 1.0;
  double max_factor = 1.0;
};

// §32.9 Table 32-5: parse the mtm_spec character string into a
// keyword. Accepts the four LRM-listed strings exactly. Unknown
// strings leave `out` unchanged and return false so the caller can
// fall through to the LRM default (TOOL_CONTROL) instead of silently
// reinterpreting an unrecognised value as some other slot.
bool ParseSdfMtmKeyword(std::string_view text, SdfMtmKeyword& out);

// §32.9 Table 32-5 row "TOOL_CONTROL (default)": collapse a parsed
// mtm_spec keyword down to the SdfMtm slot that downstream code
// consumes. The three named keywords map directly; kToolControl
// hands back the caller-supplied `tool_default`, which represents
// "the value as selected by the simulator". This split lets the
// SdfMtm enum stay free of knowledge about the simulator's
// delay-mode option.
SdfMtm ResolveSdfMtm(SdfMtmKeyword keyword, SdfMtm tool_default);

// §32.9 Table 32-6: parse the scale_type character string into a
// keyword. Accepts the four LRM-listed strings exactly. Unknown
// strings leave `out` unchanged and return false so the caller can
// fall through to the LRM default (FROM_MTM).
bool ParseSdfScaleType(std::string_view text, SdfScaleType& out);

// §32.9 scale_factors paragraph: parse a "min:typ:max" triple-of-
// reals string into the three multipliers. An empty string resets
// `out` to the LRM default 1.0:1.0:1.0 so a caller threading
// optional arguments can pass the empty string through whenever the
// $sdf_annotate invocation omitted scale_factors. Returns false only
// when the text contained unparseable characters where a real number
// was expected; missing trailing slots inherit the prior default,
// matching the SDF rvalue convention.
bool ParseSdfScaleFactors(std::string_view text, SdfScaleFactors& out);

// §32.9 scale_type + scale_factors: produce the post-scaling SDF
// triplet from `value`. FROM_MTM scales each slot independently; the
// three single-source forms broadcast the named source value through
// the three multipliers. Each output slot is rounded to the nearest
// integer tick (banker's rounding via static_cast after +0.5 on
// non-negative values), matching the LRM's expectation that
// annotated delays remain integer time ticks after scaling.
SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors);

// §32.9 scale_factors / scale_type composition helper: walk every
// SdfDelayValue inside `file` (IOPATH delays, INTERCONNECT delays,
// pulse limits, timing-check limits, specparam values) through
// ApplySdfScaling and return a fresh SdfFile carrying the scaled
// triplets. The original file is unchanged so callers can reuse the
// raw parse output for diagnostics or per-region rescaling.
SdfFile ScaleSdfFile(const SdfFile& file, SdfScaleType type,
                     const SdfScaleFactors& factors);

// §32.9 paragraph "log_file": "Each individual annotation of timing
// data from the SDF file results in an entry in the log file." Walk
// every backannotation construct in `file` (IOPATH, INTERCONNECT,
// PATHPULSE, TIMINGCHECK, LABEL/SPECPARAM) and emit one human-readable
// line per construct to `log_path`. Each line names the construct
// kind and the timing data that was annotated (port pair / signal
// names plus the typical-slot delay or limit), so the log is a
// faithful per-annotation trail of "timing data" rather than just a
// list of construct names. Returns false when the log file cannot be
// opened. An empty `log_path` is a no-op returning true so the
// surrounding annotation flow can pass the path through
// unconditionally regardless of whether the caller wanted a log.
bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path);

// §32.9 paragraph "config_file": a configuration file may carry
// MTM_SPEC, SCALE_FACTORS, and SCALE_TYPE keywords that the LRM
// names as the targets of the explicit-argument override rules
// (R14/R19/R22). The format of the configuration file itself is
// vendor-defined and outside §32.9's scope; this struct is the
// minimal surface a hypothetical config-file parser must populate to
// participate in the override resolution below. Empty fields signal
// "the configuration file did not name this keyword", letting the
// resolver fall through to the LRM default.
struct SdfAnnotateConfig {
  std::string mtm_spec;
  std::string scale_factors;
  std::string scale_type;
};

// §32.9 mtm_spec / scale_factors / scale_type paragraphs: the parsed
// final values the annotator should use for one $sdf_annotate
// invocation, after the override rules have been resolved. Carries
// each of the three argument categories in the typed form the
// downstream pipeline consumes.
struct ResolvedSdfAnnotateArgs {
  SdfMtmKeyword mtm = SdfMtmKeyword::kToolControl;
  SdfScaleFactors factors;
  SdfScaleType scale_type = SdfScaleType::kFromMtm;
};

// §32.9 R14 (mtm_spec) + R19 (scale_factors) + R22 (scale_type): the
// explicit arguments to $sdf_annotate override any matching keyword
// supplied by the configuration file. This helper applies that
// precedence rule for all three argument categories in one place: a
// non-empty explicit string wins over the config-file value, a
// non-empty config-file value wins over the LRM default, and an
// unparseable string at either layer leaves the next-lower layer
// intact rather than silently substituting an unknown value. Each
// explicit_* argument is the raw string the simulator received from
// the SystemVerilog call site (empty when the position was omitted),
// `config` carries the configuration file's keyword strings (empty
// when the configuration file did not name the keyword), and the
// returned struct is the final tuple the annotator uses.
ResolvedSdfAnnotateArgs ResolveSdfAnnotateArgs(
    std::string_view explicit_mtm_spec,
    std::string_view explicit_scale_factors,
    std::string_view explicit_scale_type,
    const SdfAnnotateConfig& config);

// =============================================================================
// SDF parser
// =============================================================================

// Parse an SDF string into an SdfFile structure.
bool ParseSdf(std::string_view input, SdfFile& out);

// =============================================================================
// Delay expansion (§32.8 Table 32-4)
// =============================================================================

// §32.8 Table 32-4: extend 1/2/3/6/12 SDF delay values into the 12
// SystemVerilog transition delays of a specify path or interconnect. The
// table differs from the §30.5.1 / Table 30-3 pessimistic min/max
// derivation in several X-state slots — for example three-value SDF input
// resolves x->0 to v2 (not max(v2,v3)), x->z to v3 (not max(v1,v2)), and
// six-value input resolves x->1 to max(v1,v4) — so the SDF flow must
// route through this helper rather than the §30.5.1 expansion.
std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm);

// §32.8 sentences 5-7: reduce more-than-three SDF delays to the three
// SystemVerilog delays of a gate primitive or continuous assignment by
// keeping the first three and ignoring the rest, with the X-state delay
// derived as the minimum of those three. Returns
// {rise, fall, turnoff, x_state}; for inputs of three or fewer the
// per-slot expansion is delegated to §28.16 / Table 28-9 (this helper
// just broadcasts the supplied values into the unfilled slots), but the
// §32.8 X-state-equals-min rule still drives the fourth slot.
std::array<uint64_t, 4> ReduceSdfDelaysToThree(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm);

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
//
// §32.6 sentence 4: when `scope` is non-empty the annotator filters by
// the SDF cell INSTANCE so that only cells sitting at or hierarchically
// under the named region land on the manager. The match accepts an
// instance equal to the scope or one whose first separator-delimited
// segment is exactly the scope, so "u1" annotates "u1" and "u1/sub/dut"
// without spilling onto siblings like "u10/dut" that share a leading
// substring. An empty scope (the default) disables the filter so every
// cell is annotated, preserving the §32.5 single-call behaviour.
SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view scope = {});

}  // namespace delta
