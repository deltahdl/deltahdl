#pragma once

#include <cstdint>
#include <filesystem>
#include <string>
#include <unordered_map>
#include <vector>

#include "parser/scope_type_names.h"

namespace delta {

class Arena;
class DiagEngine;
class LibraryMap;
class SourceManager;
struct CompilationUnit;

enum class CompileOutcome : uint8_t {
  kCompiled = 0,
  kSkipped = 1,
  kFailed = 2,
};

struct WrittenCell {
  std::string library;
  std::string name;
  uint32_t file_id = 0;
};

class SinglePassCompiler {
 public:
  SinglePassCompiler(LibraryMap& lib_map, SourceManager& mgr, Arena& arena,
                     DiagEngine& diag);

  bool CompileCommandLine(const std::vector<std::filesystem::path>& files,
                          CompilationUnit& unit);

  CompileOutcome CompileSource(const std::filesystem::path& file,
                               CompilationUnit& unit);

  void SetSkipUpToDate(bool enabled) { skip_up_to_date_ = enabled; }

 private:
  struct CompiledSource {
    std::string text;
    CompilationUnit* parsed = nullptr;
    std::vector<WrittenCell> cells;
    CompilationUnitScopeNames cu_scope;
  };

  bool CellsStillHeldInLibraries(const CompiledSource& prior) const;

  CompileOutcome MapIntoLibrary(const std::string& path, std::string text,
                                CompilationUnit& unit);

  LibraryMap& lib_map_;
  SourceManager& mgr_;
  Arena& arena_;
  DiagEngine& diag_;
  bool skip_up_to_date_ = true;
  std::unordered_map<std::string, CompiledSource> compiled_;
  CompilationUnitScopeNames cu_scope_;
};

}  // namespace delta
