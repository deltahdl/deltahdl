#pragma once

#include <filesystem>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct RtlirDesign;

class SeparateCompilationBinder {
 public:
  SeparateCompilationBinder(SourceManager& mgr, Arena& arena, DiagEngine& diag);

  bool LoadLibrary(const std::filesystem::path& path);

  RtlirDesign* Bind(const std::vector<std::string_view>& top_names);

  void SetLibrarySearchOrder(std::vector<std::string> order) {
    library_order_ = std::move(order);
  }

  RtlirDesign* BindConfig(std::string_view config_name);

  struct MissingCell {
    std::string name;
    SourceLoc loc;
  };

  const std::vector<MissingCell>& CellsNotPrecompiled() const {
    return not_precompiled_;
  }

 private:
  struct Descent {
    std::unordered_set<std::string_view> reached;
    std::vector<ModuleDecl*> pending;
  };

  bool RunDescent(Descent& descent);

  bool AllCellsPrecompiled(const std::vector<std::string_view>& top_names);

  bool DesignCellsPrecompiled(const ConfigDecl* cfg);

  void ReachSubinstances(const ModuleDecl* decl, Descent& descent);

  SourceManager& mgr_;
  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit unit_;
  std::vector<MissingCell> not_precompiled_;
  std::vector<std::string> library_order_;
};

}  // namespace delta
