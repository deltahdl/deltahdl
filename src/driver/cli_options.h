#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "common/arg_origin.h"
#include "common/types.h"
#include "elaborator/elaborator_data.h"
#include "preprocessor/protect_cli.h"
#include "simulator/foreign_code.h"

namespace delta {

class SpecifyManager;

struct CliOptions {
  std::vector<std::string> source_files;
  std::vector<std::string> top_modules;
  std::string vcd_file;
  std::vector<std::string> include_dirs;

  std::vector<std::string> lib_search_order;
  std::vector<std::string> library_map_files;
  std::string config;
  std::vector<std::string> precompiled_libs;
  std::string precompile_library;
  std::string precompile_output;
  std::string sv_root;
  std::vector<std::string> sv_libs;
  std::vector<ForeignCodeLibList> sv_liblists;

  std::vector<std::pair<std::string, std::string>> defines;
  std::vector<std::string> plus_args;
  int64_t max_generate_iterations = delta::kDefaultMaxGenerateIterations;
  uint32_t seed = 0;
  bool synth_mode = false;
  bool lint_only = false;
  bool compilation_unit_per_file = false;
  bool parse_only = false;
  bool dump_ast = false;
  bool dump_ir = false;
  bool dump_aig = false;
  bool no_opt = false;
  bool werror = false;
  bool show_version = false;
  bool show_help = false;
  delta::DelayMode mintypmax = delta::DelayMode::kTyp;
  int vpi_compat_mode = 0;
  bool negative_timing_checks = false;
  bool no_timing_checks = false;
  uint8_t pulse_reject_percent = 100;
  uint8_t pulse_error_percent = 100;
  std::optional<bool> pulse_style_ondetect;
  std::optional<bool> showcancelled;
  bool rejected_argument = false;
  const ArgOrigins* arg_origins = nullptr;
  delta::ProtectCliOptions protect;
};

bool ParseArgs(int argc, char* argv[], CliOptions& opts);

void ApplyPulseControlOptions(const CliOptions& opts, SpecifyManager& mgr);

}  // namespace delta
