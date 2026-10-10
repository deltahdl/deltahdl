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

// What preprocessing the source files of a compilation unit produced: the text
// the parser reads and the directive state the preprocessor ended in.
struct PreprocResult {
  std::string source;
  // Whether a source file named on the command line could not be opened. Such
  // a file fails the run wherever it stands in the list, and empty text cannot
  // say so: a source of no bytes preprocesses to empty text too, and the text
  // gathered before a later file failed is not empty.
  bool unreadable = false;
  // The source each line of `source` was written on, which §22.12 requires a
  // compiler to maintain and which `source` does not carry: it splices in the
  // lines of every `include and joins a `define body that spanned continuation
  // lines. It travels beside `source` because the two are appended together.
  std::vector<OutputLineOrigin> line_origins;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;
  std::vector<std::string> cell_module_names;
  std::vector<ModuleDirectives> module_directives;

  uint64_t default_decay_time = 0;
  double default_decay_time_real = 0.0;
  bool default_decay_time_infinite = true;

  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  DelayModeDirective delay_mode_directive = DelayModeDirective::kNone;

  TimeScale timescale;
  bool has_global_precision = false;
  TimeUnit global_precision = TimeUnit::kNs;
  // The line of `source` each command-line source file's text begins on, in
  // command-line order. §33.3.1 maps a source file to a library, and a design
  // element belongs to the file named on the command line whose text holds
  // it, whichever file an `include put the element's own lines in.
  std::vector<std::pair<uint32_t, std::string>> file_first_lines;
  // The runtime_license expressions met in encrypted models, which §34.5.29.2
  // has asked before the model is executed.
  std::vector<ProtectRuntimeLicense> runtime_licenses;
};

// Preprocesses every file of the command line into one compilation unit, the
// use model §3.12.1 (printed page 56) names first.
PreprocResult PreprocessSources(const CliOptions& opts, SourceManager& src_mgr,
                                DiagEngine& diag,
                                ProtectLicenseLibraries& licenses);

// Parses `source`, the preprocessed text of one compilation unit.
CompilationUnit* ParseSource(const std::string& source,
                             const std::vector<OutputLineOrigin>& line_origins,
                             SourceManager& src_mgr, DiagEngine& diag,
                             Arena& arena);

// Gives `cu` the directive state its preprocessing ended in.
void ApplyPreprocMetadata(CompilationUnit* cu, const PreprocResult& pp);

// One compilation unit of the use model §3.12.1 names second, in which each
// file is a unit of its own: its parse and its preprocessing.
struct SeparateUnit {
  CompilationUnit* cu = nullptr;
  PreprocResult pp;
};

// Preprocesses and parses each file of the command line as a compilation unit
// of its own, appending each unit to `units`. A unit whose text ends inside a
// declaration extends through the files after it until none ends inside one,
// and the compiler directives of one unit do not reach the next. False where
// a file could not be read or an error was reported.
bool ParseSeparateUnits(const CliOptions& opts, SourceManager& src_mgr,
                        DiagEngine& diag, ProtectLicenseLibraries& licenses,
                        Arena& arena, std::vector<SeparateUnit>& units);

}  // namespace delta
