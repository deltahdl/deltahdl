#pragma once

#include <array>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"

namespace delta {

class SpecifyManager;

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
};

struct SdfPulseLimit {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue reject;
  SdfDelayValue error;
  bool has_error = false;
  bool is_percent = false;
};

enum class SdfDelayEntryKind : uint8_t {
  kIopath,
  kPulseLimit,
  kInterconnect,
};

struct SdfDelayEntryRef {
  SdfDelayEntryKind kind = SdfDelayEntryKind::kIopath;
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

  std::vector<SdfDelayEntryRef> delay_entry_order;
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

bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path);

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

bool ParseSdf(std::string_view input, SdfFile& out);

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

}  // namespace delta
