#pragma once

#include <array>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"

namespace delta {

class SpecifyManager;
class SimContext;

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

  std::string condition;

  bool is_ifnone = false;

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

  kBidirectskew,
  kNochange,
};

struct SdfTimingCheck {
  SdfCheckType check_type = SdfCheckType::kSetup;
  std::string ref_port;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_port;
  SpecifyEdge data_edge = SpecifyEdge::kNone;

  SdfDelayValue limit;
  SdfDelayValue limit2;

  std::string condition;
};

struct SdfSpecparam {
  std::string name;
  SdfDelayValue value;
  bool is_increment = false;
};

enum class SdfInterconnectKind : uint8_t {
  kInterconnect,
  kPort,
  kNetdelay,
};

struct SdfInterconnect {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfInterconnectKind kind = SdfInterconnectKind::kInterconnect;
  bool is_increment = false;

  // §32.4.4: an interconnect delay carries twelve transition delays, filled in
  // from the values the entry lists exactly the way a module path delay is, so
  // an entry may list one, two, three, six or twelve of them. `rise` and `fall`
  // are the first two, kept for callers that only ever want those; `values`
  // holds the whole list in the order it was written.
  std::vector<SdfDelayValue> values;
};

// §32.4.1 Table 32-1: a DEVICE entry of a DELAY section. `port_instance` is the
// optional operand naming what the delay lands on -- a module instance or one
// of its outputs; when it is empty the entry carries no operand and reaches
// every module output. The delay values follow the same rise/fall/turnoff shape
// an IOPATH uses.
struct SdfDevice {
  std::string port_instance;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfDelayValue turnoff;
  bool is_increment = false;
};

struct SdfPulseLimit {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue reject;
  SdfDelayValue error;
  bool has_error = false;
  bool is_percent = false;
};

// §32.5: which of a cell's parsed lists one construct was appended to. Every
// construct a cell can carry is enumerated here, not just the ones a DELAY
// section holds, because annotation runs over all of them in one order.
enum class SdfCellEntryKind : uint8_t {
  kIopath,
  kPulseLimit,
  kInterconnect,
  kDevice,
  kSpecparam,
  kTimingCheck,
};

struct SdfCellEntryRef {
  SdfCellEntryKind kind = SdfCellEntryKind::kIopath;
  uint32_t index = 0;
};

struct SdfCell {
  std::string cell_type;
  std::string instance;
  std::vector<SdfIopath> iopaths;
  std::vector<SdfTimingCheck> timing_checks;

  std::vector<SdfSpecparam> specparams;
  std::vector<SdfInterconnect> interconnects;

  std::vector<SdfPulseLimit> pulse_limits;

  std::vector<SdfDevice> devices;

  // §32.5: annotation is an ordered process, so a cell keeps the order its
  // constructs were written in. One construct's annotation may be changed by a
  // later one that overwrites or modifies it, and the two need not be the same
  // construct or even sit in the same section, so a single list spans every
  // section of the cell rather than one list per section.
  std::vector<SdfCellEntryRef> entry_order;
};

struct SdfFile {
  std::string version;
  std::string design;
  std::vector<SdfCell> cells;

  std::vector<std::string> unannotatable;
};

enum class SdfMtm : uint8_t {
  kMinimum,
  kTypical,
  kMaximum,
};

enum class SdfMtmKeyword : uint8_t {
  kMaximum,
  kMinimum,
  kToolControl,
  kTypical,
};

enum class SdfScaleType : uint8_t {
  kFromMtm,
  kFromMaximum,
  kFromMinimum,
  kFromTypical,
};

struct SdfScaleFactors {
  double min_factor = 1.0;
  double typ_factor = 1.0;
  double max_factor = 1.0;
};

bool ParseSdfMtmKeyword(std::string_view text, SdfMtmKeyword& out);

SdfMtm ResolveSdfMtm(SdfMtmKeyword keyword, SdfMtm tool_default);

bool ParseSdfScaleType(std::string_view text, SdfScaleType& out);

bool ParseSdfScaleFactors(std::string_view text, SdfScaleFactors& out);

SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors);

SdfFile ScaleSdfFile(const SdfFile& file, SdfScaleType type,
                     const SdfScaleFactors& factors);

// §32.9: write one entry per individual annotation the file carries. `scope` is
// the region the annotation was aimed at; cells outside it are not annotated
// and so contribute no entries. An empty scope covers the whole file.
bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path,
                           std::string_view scope = {});

struct SdfAnnotateConfig {
  std::string mtm_spec;
  std::string scale_factors;
  std::string scale_type;
};

struct ResolvedSdfAnnotateArgs {
  SdfMtmKeyword mtm = SdfMtmKeyword::kToolControl;
  SdfScaleFactors factors;
  SdfScaleType scale_type = SdfScaleType::kFromMtm;
};

ResolvedSdfAnnotateArgs ResolveSdfAnnotateArgs(
    std::string_view explicit_mtm_spec, std::string_view explicit_scale_factors,
    std::string_view explicit_scale_type, const SdfAnnotateConfig& config);

// §32.9: read the keywords a configuration file supplies for the arguments
// $sdf_annotate can also be given directly. Returns false when the named file
// cannot be opened, leaving `out` as it was.
bool ReadSdfAnnotateConfigFile(std::string_view path, SdfAnnotateConfig& out);

bool ParseSdf(std::string_view input, SdfFile& out);

// §32.9: read an SDF file named by the sdf_file argument of $sdf_annotate and
// parse it. Returns false when the file cannot be opened or does not parse.
bool ReadSdfFile(std::string_view path, SdfFile& out);

// §32.9 Syntax 32-1: one $sdf_annotate call's operands, each already reduced
// from its expression to the text it names. An operand left out of the call is
// empty here, which is also how a call writes an operand it skips over on its
// way to a later one.
struct SdfAnnotateTaskArgs {
  std::string sdf_file;
  std::string module_instance;
  std::string config_file;
  std::string log_file;
  std::string mtm_spec;
  std::string scale_factors;
  std::string scale_type;
};

std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm);

std::array<uint64_t, 4> ReduceSdfDelaysToThree(
    const std::vector<SdfDelayValue>& vals, SdfMtm mtm);

struct SdfAnnotationResult {
  std::vector<std::string> warnings;
};

SdfAnnotationResult AnnotateSdfToManager(const SdfFile& file,
                                         SpecifyManager& mgr, SdfMtm mtm,
                                         std::string_view scope = {});

// §32.9: carry out one $sdf_annotate call. The named SDF file is read, the
// configuration file's keywords are taken and then overridden by whichever of
// mtm_spec / scale_factors / scale_type the call itself supplied, the values
// are scaled, and what is left is annotated into the region module_instance
// names. `tool_default` is the min/typ/max member the simulator picks when the
// call leaves the choice to it (Table 32-5, TOOL_CONTROL).
//
// §32.6: `mgr` carries whatever earlier calls already annotated, so a run of
// calls against one manager is how more than one SDF file is annotated: an
// ABSOLUTE value overwrites what an earlier file left and an INCREMENT value
// modifies it.
SdfAnnotationResult RunSdfAnnotateTask(const SdfAnnotateTaskArgs& args,
                                       SpecifyManager& mgr,
                                       SdfMtm tool_default = SdfMtm::kTypical);

// §32.9: the hierarchical name a module_instance operand writes, rebuilt as
// text from its expression form. Array indices are permitted, so an indexed
// instance keeps its index, with the index expression evaluated to the element
// it selects.
std::string SdfAnnotateScopeName(const Expr* e, SimContext& ctx, Arena& arena);

// §32.9: run a parsed $sdf_annotate call against the SpecifyManager bound to
// `ctx`. Returns false when the call names no SDF file or nothing is bound to
// annotate into.
bool EvalSdfAnnotateTask(const Expr* call, SimContext& ctx, Arena& arena);

}  // namespace delta
