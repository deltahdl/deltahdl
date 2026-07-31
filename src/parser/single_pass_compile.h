#pragma once

#include <cstdint>
#include <filesystem>
#include <string>
#include <unordered_map>
#include <vector>

namespace delta {

class Arena;
class DiagEngine;
class LibraryMap;
class SourceManager;
struct CompilationUnit;

// §33.5.1: what became of one source description named on the command line.
enum class CompileOutcome : uint8_t {
  // Parsed, and every cell it declares written into that file's library.
  kCompiled = 0,
  // Its cells were already held in their libraries, compiled from this same
  // text, so they were not compiled a second time.
  kSkipped = 1,
  // The file could not be read, belonged to no single library, or did not
  // parse. Nothing of it reached a library.
  kFailed = 2,
};

// §33.5.1: one cell as a compiler wrote it into a library -- the library it
// went into, the name it was written under, and the source description that
// put it there. A later description writing the same name into the same
// library displaces this one, and comparing the recorded source description
// against what the library now holds is how that displacement is noticed.
struct WrittenCell {
  std::string library;
  std::string name;
  uint32_t file_id = 0;
};

// §33.5.1: the traditional, single-pass use model. Every source description
// the design may bind against is named on the command line and nothing else is
// read; compiling one parses it and writes every cell it declares into the
// library that file maps to, whether or not any instance in the design turns
// out to name that cell. The cells accumulate into one compilation unit, which
// is what the top-level cell is then located in (§23.3.1) and what every
// instance below it binds against.
//
// A cell already held in its library, compiled from a source description whose
// text has not changed since, need not be compiled again. That check is the
// tool's to make rather than the standard's to require, so SetSkipUpToDate
// turns it off; with it off, every named description is compiled afresh.
class SinglePassCompiler {
 public:
  SinglePassCompiler(LibraryMap& lib_map, SourceManager& mgr, Arena& arena,
                     DiagEngine& diag);

  // Compiles a whole command line in the order given, appending the cells of
  // every named description to `unit`. Every file is attempted even after one
  // has failed, so a run names each description it could not use rather than
  // only the first. A description named more than once on one command line is
  // still one description and contributes its cells once. Returns false if any
  // file failed. Pass a compilation unit that no earlier command line has
  // already been compiled into.
  bool CompileCommandLine(const std::vector<std::filesystem::path>& files,
                          CompilationUnit& unit);

  // Compiles one named source description, appending its cells to `unit`.
  CompileOutcome CompileSource(const std::filesystem::path& file,
                               CompilationUnit& unit);

  void SetSkipUpToDate(bool enabled) { skip_up_to_date_ = enabled; }

 private:
  // A source description this compiler has already compiled: the text it held
  // when it was compiled, the parse that produced its cells, and where those
  // cells went. Handing the same parse to a later command line is what
  // skipping a recompile amounts to.
  struct CompiledSource {
    std::string text;
    CompilationUnit* parsed = nullptr;
    std::vector<WrittenCell> cells;
  };

  // True when every cell `prior` wrote is still the cell its library holds
  // under that name. False once another description has written over one of
  // them, because the library then no longer holds what `prior` compiled.
  bool CellsStillHeldInLibraries(const CompiledSource& prior) const;

  // Parses one description and maps its cells into its library, whether or not
  // the design being built has any use for them.
  CompileOutcome MapIntoLibrary(const std::string& path, std::string text,
                                CompilationUnit& unit);

  LibraryMap& lib_map_;
  SourceManager& mgr_;
  Arena& arena_;
  DiagEngine& diag_;
  bool skip_up_to_date_ = true;
  std::unordered_map<std::string, CompiledSource> compiled_;
};

}  // namespace delta
