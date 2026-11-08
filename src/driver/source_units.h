#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "driver/cli_options.h"
#include "driver/protect_license_libraries.h"
#include "preprocessor/preprocessor.h"

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct CompilationUnit;

struct PreprocResult {
  std::string source;
  bool unreadable = false;
  std::vector<OutputLineOrigin> line_origins;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;
  std::vector<std::string> cell_module_names;
  std::vector<ModuleDirectives> module_directives;

  uint64_t default_decay_time = 0;
  double default_decay_time_real = 0.0;
  bool default_decay_time_infinite = true;
  bool default_decay_time_is_real = false;

  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  DelayModeDirective delay_mode_directive = DelayModeDirective::kNone;

  bool has_global_precision = false;
  TimeUnit global_precision = TimeUnit::kNs;
  int global_precision_magnitude = 1;
  std::vector<std::pair<uint32_t, std::string>> file_first_lines;
  std::vector<ProtectRuntimeLicense> runtime_licenses;
};

PreprocResult PreprocessSources(const CliOptions& opts, SourceManager& src_mgr,
                                DiagEngine& diag,
                                ProtectLicenseLibraries& licenses);

CompilationUnit* ParseSource(const PreprocResult& pp, SourceManager& src_mgr,
                             DiagEngine& diag, Arena& arena);

void ApplyPreprocMetadata(CompilationUnit* cu, const PreprocResult& pp);

struct SeparateUnit {
  CompilationUnit* cu = nullptr;
  PreprocResult pp;
};

struct SeparateUnits {
  std::vector<SeparateUnit> units;
  bool read = false;
};

SeparateUnits ParseSeparateUnits(const CliOptions& opts, SourceManager& src_mgr,
                                 DiagEngine& diag,
                                 ProtectLicenseLibraries& licenses,
                                 Arena& arena);

}  // namespace delta
