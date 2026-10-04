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
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "parser/precompiled_library.h"
#include "preprocessor/preprocessor.h"

namespace delta {

PreprocConfig PreprocConfigFor(const CliOptions& opts) {
  PreprocConfig config;
  config.include_dirs = opts.include_dirs;
  config.defines = opts.defines;
  // §34.3 (printed page 949): a tool processing source text decrypts the
  // decryption envelopes it meets with the key the user supplies, so the keys
  // given on the command line are the ones a reading run opens them with, as
  // an --encrypt run seals them under the same two.
  config.protect_key = opts.protect.exchange_key;
  config.protect_keys = opts.protect.keys;
  return config;
}

namespace {

// One source description as the preprocessor gave it back: the text, the
// origin of each of its lines, and the directive state recorded while it was
// read.
struct PreprocessedSource {
  std::string path;
  std::string text;
  std::vector<OutputLineOrigin> line_origins;
  PrecompiledDirectives directives;
};

// The contents of `path`, or nothing where it cannot be opened, which is
// reported.
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

// The entries `all` gained since it held `before`.
template <typename T>
std::vector<T> Since(const std::vector<T>& all, size_t before) {
  return {all.begin() + static_cast<std::ptrdiff_t>(before), all.end()};
}

// Preprocesses the file at `path` with `preproc`, which carries macros and
// directive state from the files before it as an ordinary compile's does, and
// keeps the parts of the preprocessor's records this file added.
std::optional<PreprocessedSource> PreprocessOne(const std::string& path,
                                                Preprocessor& preproc,
                                                SourceManager& src_mgr) {
  std::optional<std::string> content = ReadSource(path);
  if (!content || content->empty()) return std::nullopt;
  uint32_t file_id = src_mgr.AddFile(path, std::move(*content));
  size_t origins = preproc.LineOrigins().size();
  size_t modules = preproc.ModuleDirectivesList().size();
  size_t cells = preproc.CellModuleNames().size();
  PreprocessedSource out;
  out.path = path;
  out.text = preproc.Preprocess(file_id);
  out.line_origins = Since(preproc.LineOrigins(), origins);
  out.directives.modules = Since(preproc.ModuleDirectivesList(), modules);
  out.directives.cell_modules = Since(preproc.CellModuleNames(), cells);
  return out;
}

// Parses `source` once, its reports going to `diag` at the file and line each
// came from, as an ordinary compile's parse reports them. Answers whether it
// parsed without error.
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

// §33.3.1 (printed page 937): "In the case where multiple modules with the
// same name are mapped to the same library in a single invocation of the
// compiler, then a warning shall be issued." The last is the one the library
// keeps (PrecompiledLibrary::Load); a cell written by an earlier invocation
// is recompiled rather than duplicated, and draws none.
void WarnRecompiledInThisInvocation(const PreprocessedSource& source,
                                    const CliOptions& opts,
                                    std::unordered_set<std::string>& written,
                                    DiagEngine& diag) {
  for (const auto& name : PrecompiledLibrary::CellNames(source.text)) {
    if (written.insert(name).second) continue;
    // Joined rather than std::format'ed: main shall throw nothing, and
    // std::format is declared to throw format_error.
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
  // Both options are required together. A library name with nowhere to write
  // it leaves nothing that persists, and a file with no library name holds
  // cells belonging to no library, which §33.5.3 has a bind select from.
  if (opts.precompile_library.empty() || opts.precompile_output.empty()) {
    std::cerr << "--precompile-into and --precompile-out are used together\n";
    return 1;
  }
  Preprocessor preproc(src_mgr, diag, PreprocConfigFor(opts));
  std::vector<PreprocessedSource> sources;
  for (const auto& path : opts.source_files) {
    std::optional<PreprocessedSource> source =
        PreprocessOne(path, preproc, src_mgr);
    if (!source) return 1;
    sources.push_back(std::move(*source));
  }
  // A `begin_keywords region may span source file boundaries (§22.14).
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
