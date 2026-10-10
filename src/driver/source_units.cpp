#include "driver/source_units.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "driver/precompile_run.h"
#include "driver/protect_license_libraries.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "parser/scope_type_names.h"
#include "preprocessor/preprocessor.h"

namespace delta {

namespace {

// Appends the file at `path`, preprocessed, to `result`, noting the line its
// text begins on. False where the file could not be read.
bool PreprocessFile(const std::string& path, Preprocessor& preproc,
                    SourceManager& src_mgr, PreprocResult& result) {
  std::optional<std::string> content = ReadSource(path);
  if (!content) {
    result.unreadable = true;
    return false;
  }
  auto file_id = src_mgr.AddFile(path, std::move(*content));
  auto first_line = static_cast<uint32_t>(
      std::count(result.source.begin(), result.source.end(), '\n') + 1);
  result.file_first_lines.emplace_back(first_line, path);
  result.source += preproc.Preprocess(file_id);
  return true;
}

// The directive state `preproc` ends a compilation unit in.
void ReadPreprocessorState(const Preprocessor& preproc, PreprocResult& result) {
  result.default_nettype = preproc.DefaultNetType();
  result.unconnected_drive = preproc.UnconnectedDrive();
  result.cell_module_names = preproc.CellModuleNames();
  result.module_directives = preproc.ModuleDirectivesList();
  result.default_decay_time = preproc.DefaultDecayTime();
  result.default_decay_time_real = preproc.DefaultDecayTimeReal();
  result.default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  result.default_trireg_strength = preproc.DefaultTriregStrength();
  result.has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  result.delay_mode_directive = preproc.DelayModeDirective();
  result.timescale = preproc.CurrentTimescale();
  result.has_global_precision = preproc.HasGlobalPrecision();
  result.global_precision = preproc.GlobalPrecision();
  result.runtime_licenses = preproc.RuntimeLicenses();
}

// A parse of one compilation unit's text: the unit, the type names its scope
// ended with, and whether the text ended inside a declaration.
struct UnitParse {
  CompilationUnit* cu = nullptr;
  CompilationUnitScopeNames scope;
  bool ended_inside_declaration = false;
};

// Parses `pp`'s text knowing the type names `known` holds. The text is
// registered with its origins, so a report about a token of it names the file
// and line somebody can open rather than a position in a buffer they have never
// seen; the path stays <preprocessed> because it is what a position with no
// origin recorded falls back to.
UnitParse ParseUnitText(const PreprocResult& pp,
                        const CompilationUnitScopeNames& known,
                        SourceManager& src_mgr, DiagEngine& diag,
                        Arena& arena) {
  auto file_id =
      src_mgr.AddPreprocessedFile("<preprocessed>", pp.source, pp.line_origins);
  Lexer lexer(pp.source, file_id, diag, TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, arena, diag);
  parser.AdoptCompilationUnitScope(known);
  auto* cu = parser.Parse();
  return {cu, parser.CompilationUnitScope(), parser.EndedInsideDeclaration()};
}

// §3.12.1: whether `pp`'s text ends inside a declaration, asked of a trial
// parse whose reports are kept from the user, the text being parsed again once
// the unit is complete.
bool EndsInsideDeclaration(const PreprocResult& pp,
                           const CompilationUnitScopeNames& known,
                           SourceManager& src_mgr) {
  DiagEngine trial(src_mgr);
  trial.SetQuiet(true);
  Arena arena;
  return ParseUnitText(pp, known, src_mgr, trial, arena)
      .ended_inside_declaration;
}

}  // namespace

PreprocResult PreprocessSources(const CliOptions& opts, SourceManager& src_mgr,
                                DiagEngine& diag,
                                ProtectLicenseLibraries& licenses) {
  Preprocessor preproc(src_mgr, diag, PreprocConfigFor(opts, licenses.Asker()));

  PreprocResult result;
  for (const auto& path : opts.source_files) {
    if (!PreprocessFile(path, preproc, src_mgr, result)) return result;
  }
  // A `begin_keywords region may span source file boundaries (22.14), so the
  // pairing check only makes sense once every file has been preprocessed.
  preproc.ReportUnterminatedKeywordRegions();
  result.line_origins = preproc.LineOrigins();
  ReadPreprocessorState(preproc, result);
  return result;
}

CompilationUnit* ParseSource(const PreprocResult& pp, SourceManager& src_mgr,
                             DiagEngine& diag, Arena& arena) {
  return ParseUnitText(pp, {}, src_mgr, diag, arena).cu;
}

void ApplyPreprocMetadata(CompilationUnit* cu, const PreprocResult& pp) {
  cu->default_nettype = pp.default_nettype;
  cu->unconnected_drive = pp.unconnected_drive;
  MarkCellModules(cu, pp.cell_module_names);
  ApplyModuleDirectives(cu, pp.module_directives);
  cu->default_decay_time = pp.default_decay_time;
  cu->default_decay_time_real = pp.default_decay_time_real;
  cu->default_decay_time_infinite = pp.default_decay_time_infinite;
  cu->default_trireg_strength = pp.default_trireg_strength;
  cu->has_default_trireg_strength = pp.has_default_trireg_strength;
  cu->delay_mode_directive = pp.delay_mode_directive;
  cu->preproc_timescale = pp.timescale;
  cu->has_preproc_timescale = pp.has_global_precision;
  cu->preproc_global_precision = pp.global_precision;
}

SeparateUnits ParseSeparateUnits(const CliOptions& opts, SourceManager& src_mgr,
                                 DiagEngine& diag,
                                 ProtectLicenseLibraries& licenses,
                                 Arena& arena) {
  SeparateUnits result;
  auto& units = result.units;
  Preprocessor preproc(src_mgr, diag, PreprocConfigFor(opts, licenses.Asker()));
  // §3.12.1: packages and primitives are visible in every unit, so a later
  // unit's parse knows the type names the earlier units' packages and the
  // names their primitives declared, and nothing of their own scopes.
  CompilationUnitScopeNames design_wide;
  const auto& files = opts.source_files;
  size_t next = 0;
  while (next < files.size()) {
    if (!units.empty()) preproc.BeginCompilationUnit();
    SeparateUnit unit;
    const auto kFirstOrigin =
        static_cast<std::ptrdiff_t>(preproc.LineOrigins().size());
    do {
      if (!PreprocessFile(files[next++], preproc, src_mgr, unit.pp)) {
        return result;
      }
      unit.pp.line_origins.assign(
          std::next(preproc.LineOrigins().begin(), kFirstOrigin),
          preproc.LineOrigins().end());
    } while (next < files.size() &&
             EndsInsideDeclaration(unit.pp, design_wide, src_mgr));
    ReadPreprocessorState(preproc, unit.pp);
    UnitParse parsed =
        ParseUnitText(unit.pp, design_wide, src_mgr, diag, arena);
    design_wide.packages.insert(parsed.scope.packages.begin(),
                                parsed.scope.packages.end());
    design_wide.own.udps.insert(parsed.scope.own.udps.begin(),
                                parsed.scope.own.udps.end());
    unit.cu = parsed.cu;
    ApplyPreprocMetadata(unit.cu, unit.pp);
    units.push_back(std::move(unit));
  }
  preproc.ReportUnterminatedKeywordRegions();
  result.read = !diag.HasErrors();
  return result;
}

}  // namespace delta
