#include "elaborator/separate_compilation_bind.h"

#include <algorithm>
#include <filesystem>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/precompiled_library.h"

namespace delta {

namespace {

ModuleDecl* FindNamedInLibrary(const std::vector<ModuleDecl*>& decls,
                               std::string_view library,
                               std::string_view name) {
  for (auto* decl : decls) {
    if (!library.empty() && decl->library != library) continue;
    if (decl->name == name) return decl;
  }
  return nullptr;
}

ModuleDecl* FindDescendableCell(const CompilationUnit& unit,
                                std::string_view library,
                                std::string_view name) {
  if (auto* d = FindNamedInLibrary(unit.modules, library, name)) return d;
  if (auto* d = FindNamedInLibrary(unit.interfaces, library, name)) return d;
  if (auto* d = FindNamedInLibrary(unit.programs, library, name)) return d;
  return FindNamedInLibrary(unit.checkers, library, name);
}

bool HoldsPrimitive(const CompilationUnit& unit, std::string_view name) {
  for (const auto* udp : unit.udps) {
    if (udp->name == name) return true;
  }
  return false;
}

void CollectNestedCellNames(const std::vector<ModuleItem*>& items,
                            std::unordered_set<std::string_view>& names) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl) {
      if (item->nested_module_decl != nullptr) {
        names.insert(item->nested_module_decl->name);
        CollectNestedCellNames(item->nested_module_decl->items, names);
      }
      continue;
    }
    CollectNestedCellNames(item->gen_body, names);
    if (item->gen_else != nullptr) {
      CollectNestedCellNames({item->gen_else}, names);
    }
    for (const auto& gen_case : item->gen_case_items) {
      CollectNestedCellNames(gen_case.body, names);
    }
  }
}

const ConfigDecl* FindConfig(const CompilationUnit& unit,
                             std::string_view name) {
  const auto& [lib, cell] = SplitLibCell(name);
  for (const auto* cfg : unit.configs) {
    if (cfg->name == cell && (lib.empty() || cfg->library == lib)) {
      return cfg;
    }
  }
  return nullptr;
}

}  // namespace

SeparateCompilationBinder::SeparateCompilationBinder(SourceManager& mgr,
                                                     Arena& arena,
                                                     DiagEngine& diag)
    : mgr_(mgr), arena_(arena), diag_(diag) {}

bool SeparateCompilationBinder::LoadLibrary(const std::filesystem::path& path) {
  if (PrecompiledLibrary::Load(path, unit_, mgr_, arena_, diag_)) return true;
  std::string where = path.string();
  diag_.Error(SourceLoc::None(),
              std::format("no cells read from library '{}'", where),
              Subclause::None());
  return false;
}

void SeparateCompilationBinder::ReachSubinstances(const ModuleDecl* decl,
                                                  Descent& descent) {
  std::vector<InstantiatedCell> instantiated;
  CollectInstantiations(decl->items, instantiated);
  std::unordered_set<std::string_view> declared_within;
  CollectNestedCellNames(decl->items, declared_within);
  for (const auto& child : instantiated) {
    if (declared_within.contains(child.name)) continue;
    if (!descent.reached.insert(child.name).second) continue;
    auto* child_decl = FindDescendableCell(unit_, {}, child.name);
    if (child_decl != nullptr) {
      descent.pending.push_back(child_decl);
    } else if (!HoldsPrimitive(unit_, child.name)) {
      not_precompiled_.push_back({std::string(child.name), child.loc});
    }
  }
}

bool SeparateCompilationBinder::RunDescent(Descent& descent) {
  while (!descent.pending.empty()) {
    const auto* decl = descent.pending.back();
    descent.pending.pop_back();
    ReachSubinstances(decl, descent);
  }

  std::sort(not_precompiled_.begin(), not_precompiled_.end(),
            [](const MissingCell& a, const MissingCell& b) {
              return a.name < b.name;
            });
  for (const auto& missing : not_precompiled_) {
    diag_.Error(missing.loc,
                std::format("cell '{}' was not precompiled", missing.name),
                Subclause("33.5.3"));
  }
  return not_precompiled_.empty();
}

bool SeparateCompilationBinder::AllCellsPrecompiled(
    const std::vector<std::string_view>& top_names) {
  Descent descent;
  for (auto name : top_names) {
    const auto& [lib, cell] = SplitLibCell(name);
    if (!descent.reached.insert(cell).second) continue;
    auto* decl = FindDescendableCell(unit_, lib, cell);
    if (decl == nullptr) {
      not_precompiled_.push_back({std::string(name), SourceLoc::None()});
      continue;
    }
    descent.pending.push_back(decl);
  }
  return RunDescent(descent);
}

bool SeparateCompilationBinder::DesignCellsPrecompiled(const ConfigDecl* cfg) {
  Descent descent;
  for (const auto& design_cell : cfg->design_cells) {
    descent.reached.insert(design_cell.cell);
    auto* decl =
        FindDescendableCell(unit_, design_cell.library, design_cell.cell);
    if (decl == nullptr) {
      not_precompiled_.push_back(
          {std::string(design_cell.cell), design_cell.loc});
      continue;
    }
    descent.pending.push_back(decl);
  }
  return RunDescent(descent);
}

RtlirDesign* SeparateCompilationBinder::Bind(
    const std::vector<std::string_view>& top_names) {
  not_precompiled_.clear();
  if (!AllCellsPrecompiled(top_names)) return nullptr;

  Elaborator elab(arena_, diag_, &unit_);
  if (!library_order_.empty()) elab.SetLibraryDeclarationOrder(library_order_);
  return elab.Elaborate(top_names);
}

RtlirDesign* SeparateCompilationBinder::BindConfig(
    std::string_view config_name) {
  not_precompiled_.clear();

  const ConfigDecl* cfg = FindConfig(unit_, config_name);
  if (cfg == nullptr) {
    diag_.Error(SourceLoc::None(),
                std::format("config '{}' was not precompiled", config_name),
                Subclause("33.5.4"));
    return nullptr;
  }
  if (cfg->design_cells.empty()) {
    diag_.Error(cfg->range.start,
                std::format("config '{}' names no design", cfg->name),
                Subclause("33.4.1.1"));
    return nullptr;
  }

  if (!DesignCellsPrecompiled(cfg)) return nullptr;

  Elaborator elab(arena_, diag_, &unit_);
  if (!library_order_.empty()) elab.SetLibraryDeclarationOrder(library_order_);
  return elab.Elaborate(cfg);
}

}  // namespace delta
