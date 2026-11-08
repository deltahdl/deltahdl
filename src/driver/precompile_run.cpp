#include "driver/precompile_run.h"

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/envelope_viewport.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "driver/protect_license_libraries.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "parser/precompiled_library.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"

namespace delta {

PreprocConfig PreprocConfigFor(const CliOptions& opts,
                               ProtectLicenseAsk ask_license) {
  PreprocConfig config;
  config.include_dirs = opts.include_dirs;
  config.defines = opts.defines;
  config.protect_key = opts.protect.exchange_key;
  config.protect_keys = opts.protect.keys;
  config.ask_license = std::move(ask_license);
  return config;
}

std::optional<std::string> ReadSource(const std::string& path) {
  std::ifstream ifs(path);
  if (!ifs) {
    std::cerr << "error: cannot open file '" << path << "'\n";
    return std::nullopt;
  }
  std::ostringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

namespace {

struct PreprocessedSource {
  std::string path;
  std::string text;
  std::vector<OutputLineOrigin> line_origins;
  PrecompiledDirectives directives;
};

template <typename T>
std::vector<T> Since(const std::vector<T>& all, size_t before) {
  return {all.begin() + static_cast<std::ptrdiff_t>(before), all.end()};
}

PrecompiledViewport RecordedViewport(
    const EnvelopeViewport& viewport,
    const std::vector<OutputLineOrigin>& origins,
    const SourceManager& src_mgr) {
  PrecompiledViewport kept;
  kept.object = viewport.object;
  kept.access = viewport.access;
  for (std::size_t i = 0; i < origins.size(); ++i) {
    const auto kLine = static_cast<uint32_t>(i + 1);
    const SourceLoc kOrigin{origins[i].file_id, origins[i].line, 1};
    if (kept.line == 0 && kOrigin.file_id == viewport.loc.file_id &&
        kOrigin.line == viewport.loc.line) {
      kept.line = kLine;
    }
    if (!src_mgr.StandsInEnvelope(kOrigin, viewport)) continue;
    if (kept.first_line == 0) kept.first_line = kLine;
    kept.last_line = kLine;
  }
  if (kept.line == 0) kept.line = kept.first_line;
  return kept;
}

std::optional<PreprocessedSource> PreprocessOne(const std::string& path,
                                                Preprocessor& preproc,
                                                SourceManager& src_mgr) {
  std::optional<std::string> content = ReadSource(path);
  if (!content) return std::nullopt;
  uint32_t file_id = src_mgr.AddFile(path, std::move(*content));
  size_t origins = preproc.LineOrigins().size();
  size_t modules = preproc.ModuleDirectivesList().size();
  size_t cells = preproc.CellModuleNames().size();
  size_t licenses = preproc.RuntimeLicenses().size();
  size_t viewports = src_mgr.Viewports().size();
  PreprocessedSource out;
  out.path = path;
  out.text = preproc.Preprocess(file_id);
  out.line_origins = Since(preproc.LineOrigins(), origins);
  out.directives.modules = Since(preproc.ModuleDirectivesList(), modules);
  out.directives.cell_modules = Since(preproc.CellModuleNames(), cells);
  for (const ProtectRuntimeLicense& met :
       Since(preproc.RuntimeLicenses(), licenses)) {
    out.directives.runtime_licenses.push_back(met.license);
  }
  for (std::size_t i = 0; i < out.line_origins.size(); ++i) {
    const OutputLineOrigin& origin = out.line_origins[i];
    if (src_mgr.IsProtected(SourceLoc{origin.file_id, origin.line, 1})) {
      out.directives.protected_lines.push_back(static_cast<uint32_t>(i + 1));
    }
  }
  for (const EnvelopeViewport& viewport :
       Since(src_mgr.Viewports(), viewports)) {
    out.directives.viewports.push_back(
        RecordedViewport(viewport, out.line_origins, src_mgr));
  }
  return out;
}

bool ParsesWithReports(const PreprocessedSource& source, SourceManager& src_mgr,
                       DiagEngine& diag) {
  uint32_t errors = diag.ErrorCount();
  uint32_t file_id = src_mgr.AddPreprocessedFile(source.path, source.text,
                                                 source.line_origins);
  Arena arena;
  Lexer lexer(src_mgr.FileContent(file_id), file_id, diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return diag.ErrorCount() == errors;
}

void WarnRecompiledInThisInvocation(const PreprocessedSource& source,
                                    const CliOptions& opts,
                                    std::unordered_set<std::string>& written,
                                    DiagEngine& diag) {
  for (const auto& name : PrecompiledLibrary::CellNames(source.text)) {
    if (written.insert(name).second) continue;
    diag.Warning(SourceLoc::None(),
                 "'" + name + "' is compiled into library '" +
                     opts.precompile_library +
                     "' more than once in this invocation; the last one is "
                     "kept",
                 Subclause("33.3.1"));
  }
}

}  // namespace

int RunPrecompile(const CliOptions& opts, SourceManager& src_mgr,
                  DiagEngine& diag) {
  if (opts.precompile_library.empty() || opts.precompile_output.empty()) {
    std::cerr << "--precompile-into and --precompile-out are used together\n";
    return 1;
  }
  ProtectLicenseLibraries licenses;
  Preprocessor preproc(src_mgr, diag, PreprocConfigFor(opts, licenses.Asker()));
  std::vector<PreprocessedSource> sources;
  for (const auto& path : opts.source_files) {
    std::optional<PreprocessedSource> source =
        PreprocessOne(path, preproc, src_mgr);
    if (!source) return 1;
    sources.push_back(std::move(*source));
  }
  preproc.ReportUnterminatedKeywordRegions();
  if (diag.HasErrors()) return 1;

  std::unordered_set<std::string> written;
  for (const PreprocessedSource& source : sources) {
    if (!ParsesWithReports(source, src_mgr, diag)) {
      std::cerr << "could not precompile " << source.path << " into "
                << opts.precompile_output << "\n";
      return 1;
    }
    WarnRecompiledInThisInvocation(source, opts, written, diag);
    if (!PrecompiledLibrary::Save(source.text, opts.precompile_library,
                                  opts.precompile_output, source.directives)) {
      std::cerr << "could not precompile " << source.path << " into "
                << opts.precompile_output << "\n";
      return 1;
    }
  }
  return diag.HasErrors() ? 1 : 0;
}

}  // namespace delta
