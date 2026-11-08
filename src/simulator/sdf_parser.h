#pragma once

#include <array>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"

namespace delta {

class SpecifyManager;
class SimContext;

struct SdfDelayValue {
  uint64_t min_val = 0;
  uint64_t typ_val = 0;
  uint64_t max_val = 0;

  bool min_negative = false;
  bool typ_negative = false;
  bool max_negative = false;

  double min_real = 0.0;
  double typ_real = 0.0;
  double max_real = 0.0;

  bool empty = false;

  bool min_empty = false;
  bool typ_empty = false;
  bool max_empty = false;
};

struct SdfIopathDirection {
  SdfDelayValue delay;
  bool delay_present = false;
  SdfDelayValue reject;
  bool reject_present = false;
  SdfDelayValue error;
  bool error_present = false;
};

struct SdfIopath {
  std::string src_port;
  SpecifyEdge src_edge = SpecifyEdge::kNone;
  bool src_edge_known = true;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfDelayValue turnoff;
  bool is_increment = false;

  std::vector<SdfDelayValue> values;

  std::string condition;

  bool is_ifnone = false;

  bool extended_form = false;
  std::vector<SdfIopathDirection> directions;
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
  std::vector<std::pair<char, char>> ref_edge_descriptors;
  std::vector<std::pair<char, char>> data_edge_descriptors;

  SdfDelayValue limit;
  SdfDelayValue limit2;

  std::string condition;
  std::string ref_condition;
  std::string data_condition;

  std::string trailing_construct;
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

  std::vector<SdfDelayValue> values;

  std::vector<SdfIopathDirection> directions;
};

struct SdfDevice {
  std::string port_instance;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfDelayValue turnoff;
  bool is_increment = false;

  std::vector<SdfDelayValue> values;
};

struct SdfPulseLimit {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue reject;
  SdfDelayValue error;
  bool has_error = false;
  bool is_percent = false;

  bool is_increment = false;
};

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

  std::vector<SdfCellEntryRef> entry_order;
};

struct SdfFile {
  std::string version;
  std::string design;
  double timescale_seconds = 0.0;
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

bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path,
                           std::string_view region_prefix = {},
                           std::string_view design_root = {});

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

bool ReadSdfAnnotateConfigFile(std::string_view path, SdfAnnotateConfig& out);

bool ParseSdf(std::string_view input, SdfFile& out);

bool ReadSdfFile(std::string_view path, SdfFile& out);

struct SdfAnnotateTaskArgs {
  std::string sdf_file;
  std::string module_instance;

  std::string design_root;
  double precision_seconds = 0.0;
  std::string region_prefix;
  std::function<std::string_view(std::string_view)> instance_key_of_path;
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
                                         std::string_view region_prefix = {},
                                         std::string_view design_root = {});

SdfAnnotationResult RunSdfAnnotateTask(const SdfAnnotateTaskArgs& args,
                                       SpecifyManager& mgr,
                                       SdfMtm tool_default = SdfMtm::kTypical);

std::string SdfAnnotateScopeName(const Expr* e, SimContext& ctx, Arena& arena);

std::optional<std::string> SdfCellPrefixInRegion(std::string_view instance,
                                                 std::string_view region_prefix,
                                                 std::string_view design_root);

bool EvalSdfAnnotateTask(const Expr* call, SimContext& ctx, Arena& arena);

}  // namespace delta
