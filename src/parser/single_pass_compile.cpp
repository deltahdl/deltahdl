#include "parser/single_pass_compile.h"

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <ios>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/parser.h"
#include "parser/scope_type_names.h"

namespace delta {

namespace {

bool ReadWholeFile(const std::filesystem::path& path, std::string& text) {
  std::error_code ec;
  if (!std::filesystem::is_regular_file(path, ec)) return false;
  std::ifstream ifs(path, std::ios::binary);
  if (!ifs.good()) return false;
  std::ostringstream buf;
  buf << ifs.rdbuf();
  text = buf.str();
  return true;
}

std::string JoinLibraryNames(const std::vector<std::string_view>& names) {
  std::string joined;
  for (auto name : names) {
    if (!joined.empty()) joined += ", ";
    joined.append(name);
  }
  return joined;
}

struct CellWriteSink {
  LibraryMap& libs;
  DiagEngine& diag;
  std::vector<WrittenCell>& written;
};

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

void ReportCuTimescaleConflict(DiagEngine& diag, const CompilationUnit& target,
                               const CompilationUnit& src) {
  if (target.has_cu_timeunit && src.has_cu_timeunit &&
      (target.cu_time_unit != src.cu_time_unit ||
       target.cu_time_unit_magnitude != src.cu_time_unit_magnitude)) {
    diag.Error(src.cu_timeunit_loc, "timeunit does not match prior declaration",
               Subclause("3.14.2.2"));
  }
  if (target.has_cu_timeprecision && src.has_cu_timeprecision &&
      (target.cu_time_prec != src.cu_time_prec ||
       target.cu_time_prec_magnitude != src.cu_time_prec_magnitude)) {
    diag.Error(src.cu_timeprecision_loc,
               "timeprecision does not match prior declaration",
               Subclause("3.14.2.2"));
  }
}

}  // namespace

SinglePassCompiler::SinglePassCompiler(LibraryMap& lib_map, SourceManager& mgr,
                                       Arena& arena, DiagEngine& diag)
    : lib_map_(lib_map), mgr_(mgr), arena_(arena), diag_(diag) {
  lib_map.ResolvePositionsAgainst(mgr);
}

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
  std::string_view library = lib_map_.LibraryForFile(path);
  if (library.empty()) {
    diag_.Error(lib_map_.FirstDeclarationClaiming(path),
                "source description claimed by more than one library (" +
                    JoinLibraryNames(lib_map_.LibrariesForFile(path)) +
                    "): " + path,
                Subclause("33.3.1.1"));
    return CompileOutcome::kFailed;
  }

  uint32_t fid = mgr_.AddFile(path, text);
  Lexer lexer(mgr_.FileContent(fid), fid, diag_);
  Parser parser(lexer, arena_, diag_);
  parser.AdoptCompilationUnitScope(cu_scope_);
  uint32_t errors_before = diag_.ErrorCount();
  auto* parsed = parser.Parse();
  if (parsed == nullptr) return CompileOutcome::kFailed;
  if (diag_.ErrorCount() != errors_before) return CompileOutcome::kFailed;
  lib_map_.TagCompilationUnit(*parsed, path);

  CompiledSource entry;
  entry.text = std::move(text);
  entry.parsed = parsed;
  CellWriteSink sink{lib_map_, diag_, entry.cells};
  WriteCellsOfKind(parsed->modules, true, sink);
  WriteCellsOfKind(parsed->interfaces, false, sink);
  WriteCellsOfKind(parsed->programs, false, sink);
  WriteCellsOfKind(parsed->checkers, false, sink);
  WriteCellsOfKind(parsed->udps, false, sink);
  WriteCellsOfKind(parsed->packages, false, sink);
  WriteCellsOfKind(parsed->configs, false, sink);

  AppendCellDeclarations(unit, *parsed);
  ReportCuTimescaleConflict(diag_, unit, *parsed);
  AppendCompilationUnitDeclarations(unit, *parsed);
  entry.cu_scope = parser.CompilationUnitScope();
  cu_scope_ = entry.cu_scope;
  compiled_[path] = std::move(entry);
  return CompileOutcome::kCompiled;
}

CompileOutcome SinglePassCompiler::CompileSource(
    const std::filesystem::path& file, CompilationUnit& unit) {
  std::string path = file.string();
  std::string text;
  if (!ReadWholeFile(file, text)) {
    diag_.Error(SourceLoc::None(), "cannot read source description: " + path,
                Subclause::None());
    return CompileOutcome::kFailed;
  }

  auto prior = compiled_.find(path);
  bool reusable = skip_up_to_date_ && prior != compiled_.end() &&
                  prior->second.text == text &&
                  CellsStillHeldInLibraries(prior->second);
  if (reusable) {
    AppendCellDeclarations(unit, *prior->second.parsed);
    ReportCuTimescaleConflict(diag_, unit, *prior->second.parsed);
    AppendCompilationUnitDeclarations(unit, *prior->second.parsed);
    MergeCompilationUnitScope(cu_scope_, prior->second.cu_scope);
    return CompileOutcome::kSkipped;
  }
  return MapIntoLibrary(path, std::move(text), unit);
}

bool SinglePassCompiler::CompileCommandLine(
    const std::vector<std::filesystem::path>& files, CompilationUnit& unit) {
  lib_map_.BeginNewInvocation();
  cu_scope_ = CompilationUnitScopeNames{};
  std::unordered_set<std::string> named;
  bool ok = true;
  for (const auto& file : files) {
    if (!named.insert(file.string()).second) continue;
    if (CompileSource(file, unit) == CompileOutcome::kFailed) ok = false;
  }
  return ok;
}

}  // namespace delta
