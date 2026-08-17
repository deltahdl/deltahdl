#include "parser/single_pass_compile.h"

#include <filesystem>
#include <fstream>
#include <ios>
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

// The libraries claiming one source description, written out as a list for a
// diagnostic to name them in. Naming them is what tells a reader which two
// declarations of the library map have to be reconciled, and it tells a caller
// reading the diagnostic back that the compile stopped on the ambiguity rather
// than on any of the other things that stop a compile.
std::string JoinLibraryNames(const std::vector<std::string_view>& names) {
  std::string joined;
  for (auto name : names) {
    if (!joined.empty()) joined += ", ";
    joined.append(name);
  }
  return joined;
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
    : lib_map_(lib_map), mgr_(mgr), arena_(arena), diag_(diag) {
  // A report this compiler makes about a library declaration stands at a
  // position `diag` resolves through `mgr`, so the map file the declaration is
  // written in has to be a file `mgr` holds. Handing the map this manager here
  // is what puts it there, and it is done at construction because a map file is
  // loaded before anything is compiled out of it.
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
  // A description that several library declarations claim equally belongs to
  // no one library, so there is nowhere to map its cells to.
  std::string_view library = lib_map_.LibraryForFile(path);
  if (library.empty()) {
    // The report stands at the first of the library declarations claiming the
    // description. §33.3.1.1 makes the claim an error without singling out one
    // of the declarations that make it, so the message names every claimant and
    // the position picks the one a reader of the map file reaches first, which
    // is the same declaration on every run.
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
  // The compilation-unit scope the descriptions before this one on the command
  // line built up, because §3.12.1 case a) makes their declarations "accessible
  // following normal visibility rules throughout the entire set of files" and
  // a type name has to be known while the file is parsed rather than after it.
  // `byte_t b;` parses as an instantiation of a module called byte_t until the
  // parser is told byte_t is a type.
  parser.AdoptCompilationUnitTypeNames(cu_type_names_);
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
  //
  // All seven design element kinds, in the order AppendCellDeclarations in
  // src/parser/ast_design.h moves them. §33.2.1 rules that "a library is a
  // named collection of cells" and that "a cell is a design element (see 3.2),
  // such as a module, primitive, interface, program, package, or
  // configuration"; its six are introduced by "such as", and §3.2 names seven:
  // "a SystemVerilog module (see Clause 23), program (see Clause 24), interface
  // (see Clause 25), checker (see Clause 17), package (see Clause 26),
  // primitive (see Clause 28) or configuration (see Clause 33)". The two lists
  // read the same way down the page because they answer the same question, and
  // the checker went missing from this one while the other had it.
  WriteCellsOfKind(parsed->modules, /*is_module=*/true, sink);
  WriteCellsOfKind(parsed->interfaces, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->programs, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->checkers, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->udps, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->packages, /*is_module=*/false, sink);
  WriteCellsOfKind(parsed->configs, /*is_module=*/false, sink);

  // The cells and the compilation-unit scope both, because this compiler is
  // §3.12.1 case a): "all files on a given compilation command line make a
  // single compilation unit (in which case the declarations within those files
  // are accessible following normal visibility rules throughout the entire set
  // of files)". A typedef, class, bind or out-of-block constraint this
  // description wrote outside every design element is such a declaration, and
  // dropping it would hide it from the rest of the command line and from this
  // description itself, since the unit built here is the only one elaboration
  // reads.
  AppendCellDeclarations(unit, *parsed);
  AppendCompilationUnitDeclarations(unit, *parsed);
  // The parse started from cu_type_names_, so what it ends holding is that set
  // plus whatever this description added to the compilation-unit scope.
  entry.cu_type_names = parser.CompilationUnitTypeNames();
  cu_type_names_ = entry.cu_type_names;
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
    // Not recompiling a cell is not the same as dropping it: the parse the
    // earlier compile produced is what this unit gains, so the design still
    // binds against the cell. Its compilation-unit scope comes over for the
    // same reason, and out of the same parse, so what a description
    // contributes to the unit does not turn on whether this run compiled it or
    // an earlier one did.
    AppendCellDeclarations(unit, *prior->second.parsed);
    AppendCompilationUnitDeclarations(unit, *prior->second.parsed);
    cu_type_names_.types.insert(prior->second.cu_type_names.types.begin(),
                                prior->second.cu_type_names.types.end());
    cu_type_names_.nettypes.insert(prior->second.cu_type_names.nettypes.begin(),
                                   prior->second.cu_type_names.nettypes.end());
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
  // A command line is a compilation unit (§3.12.1 case a)), so its
  // compilation-unit scope starts empty however many command lines this
  // compiler has already run.
  cu_type_names_ = ScopeTypeNames{};
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
