#include "parser/single_pass_compile.h"

#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_set>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

namespace delta {

namespace {

bool ReadWholeFile(const std::filesystem::path& path, std::string& text) {
  // A directory, or a device, named where a source description was expected
  // opens without complaint on some platforms and then yields no bytes. Left
  // to the read alone it would pass for a description that happens to declare
  // no cells, and the command line would look like it had been honoured.
  std::error_code ec;
  if (!std::filesystem::is_regular_file(path, ec)) return false;
  std::ifstream ifs(path, std::ios::binary);
  if (!ifs.good()) return false;
  std::ostringstream buf;
  buf << ifs.rdbuf();
  text = buf.str();
  return true;
}

// The library-writing side of compiling one source description: the map that
// receives the cells, the engine that reports a collision between them, and
// the record of what was written. These travel together so that one traversal
// serves every kind of cell a description can declare.
struct CellWriteSink {
  LibraryMap& libs;
  DiagEngine& diag;
  std::vector<WrittenCell>& written;
};

// Writes every declaration of one cell kind into the library its source
// description was mapped to, and records the identity of each write so that a
// later run can tell whether the library still holds this description's cell.
template <typename Decl>
void WriteCellsOfKind(const std::vector<Decl*>& decls, bool is_module,
                      CellWriteSink& sink) {
  for (const auto* decl : decls) {
    SourceLoc loc = decl->range.start;
    sink.libs.WriteCell(decl->library, decl->name, is_module, loc, sink.diag);
    WrittenCell record;
    record.library = decl->library;
    record.name = decl->name;
    record.file_id = loc.file_id;
    sink.written.push_back(std::move(record));
  }
}

}  // namespace

SinglePassCompiler::SinglePassCompiler(LibraryMap& lib_map, SourceManager& mgr,
                                       Arena& arena, DiagEngine& diag)
    : lib_map_(lib_map), mgr_(mgr), arena_(arena), diag_(diag) {}

bool SinglePassCompiler::CellsStillHeldInLibraries(
    const CompiledSource& prior) const {
  for (const auto& cell : prior.cells) {
    const LibraryCell* held = lib_map_.CellInLibrary(cell.library, cell.name);
    if (held == nullptr) return false;
    if (held->loc.file_id != cell.file_id) return false;
  }
  return true;
}

CompileOutcome SinglePassCompiler::MapIntoLibrary(const std::string& path,
                                                  std::string text,
                                                  CompilationUnit& unit) {
  // A description that several library declarations claim equally belongs to
  // no one library, so there is nowhere to map its cells to.
  std::string_view library = lib_map_.LibraryForFile(path);
  if (library.empty()) {
    diag_.Error({}, "source description claimed by two libraries: " + path);
    return CompileOutcome::kFailed;
  }

  uint32_t fid = mgr_.AddFile(path, text);
  Lexer lexer(mgr_.FileContent(fid), fid, diag_);
  Parser parser(lexer, arena_, diag_);
  // Errors already on the engine belong to descriptions compiled earlier in
  // the run, so it is the errors this parse adds that decide its outcome.
  uint32_t errors_before = diag_.ErrorCount();
  auto* parsed = parser.Parse();
  if (parsed == nullptr) return CompileOutcome::kFailed;
  if (diag_.ErrorCount() != errors_before) return CompileOutcome::kFailed;
  lib_map_.TagCompilationUnit(*parsed, path);

  CompiledSource entry;
  entry.text = std::move(text);
  entry.parsed = parsed;
  CellWriteSink sink{lib_map_, diag_, entry.cells};
  // Every cell the description declares goes into the library, whether or not
  // the design being built instantiates it. Only a module collides with
  // another module of its name loudly enough to warn about (§33.3.1.1).
  WriteCellsOfKind(parsed->modules, /*is_module=*/true, sink);
  WriteCellsOfKind(parsed->interfaces, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->programs, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->udps, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->packages, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->configs, /*is_module=*/false, sink);

  AppendCellDeclarations(unit, *parsed);
  compiled_[path] = std::move(entry);
  return CompileOutcome::kCompiled;
}

CompileOutcome SinglePassCompiler::CompileSource(
    const std::filesystem::path& file, CompilationUnit& unit) {
  std::string path = file.string();
  std::string text;
  if (!ReadWholeFile(file, text)) {
    diag_.Error({}, "cannot read source description: " + path);
    return CompileOutcome::kFailed;
  }

  auto prior = compiled_.find(path);
  bool reusable = skip_up_to_date_ && prior != compiled_.end() &&
                  prior->second.text == text &&
                  CellsStillHeldInLibraries(prior->second);
  if (reusable) {
    // Not recompiling a cell is not the same as dropping it: the parse the
    // earlier compile produced is what this unit gains, so the design still
    // binds against the cell.
    AppendCellDeclarations(unit, *prior->second.parsed);
    return CompileOutcome::kSkipped;
  }
  return MapIntoLibrary(path, std::move(text), unit);
}

bool SinglePassCompiler::CompileCommandLine(
    const std::vector<std::filesystem::path>& files, CompilationUnit& unit) {
  // Whatever the libraries already hold was put there by an earlier command
  // line, so meeting one of those names again is a recompile rather than two
  // descriptions of one cell within a single run (§33.3.1.1).
  lib_map_.BeginNewInvocation();
  std::unordered_set<std::string> named;
  bool ok = true;
  for (const auto& file : files) {
    // One description named twice -- two option files listing a common source,
    // say -- is still one description. Letting it through a second time would
    // put a second copy of each of its cells into the unit the design binds
    // in, so a repeated command-line entry would build a design declaring
    // every one of those cells twice.
    if (!named.insert(file.string()).second) continue;
    if (CompileSource(file, unit) == CompileOutcome::kFailed) ok = false;
  }
  return ok;
}

}  // namespace delta
