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
#include "parser/ast.h"
#include "parser/precompiled_library.h"

namespace delta {

namespace {

// The declaration named `name` among `decls`, or nullptr. An empty `library`
// asks for a cell of that name wherever it was compiled; a library named
// confines the answer to the cells compiled into it, so a name several
// libraries hold cells under picks out the one that library holds.
ModuleDecl* FindNamedInLibrary(const std::vector<ModuleDecl*>& decls,
                               std::string_view library,
                               std::string_view name) {
  for (auto* decl : decls) {
    if (!library.empty() && decl->library != library) continue;
    if (decl->name == name) return decl;
  }
  return nullptr;
}

// The declaration a descent continues into for the cell named `name`: the
// instantiable cell kinds whose bodies can hold further instances, every one
// of which a compiled form holds as a module declaration. Returns nullptr when
// no loaded cell of one of those kinds answers to the name in `library`.
ModuleDecl* FindDescendableCell(const CompilationUnit& unit,
                                std::string_view library,
                                std::string_view name) {
  if (auto* d = FindNamedInLibrary(unit.modules, library, name)) return d;
  if (auto* d = FindNamedInLibrary(unit.interfaces, library, name)) return d;
  if (auto* d = FindNamedInLibrary(unit.programs, library, name)) return d;
  return FindNamedInLibrary(unit.checkers, library, name);
}

// True when a loaded cell named `name` is a primitive. A primitive is the
// instantiable cell kind that holds no instances of its own, so reaching one
// ends that branch of the descent: it has been compiled, and there is nothing
// below it to ask after.
bool HoldsPrimitive(const CompilationUnit& unit, std::string_view name) {
  for (const auto* udp : unit.udps) {
    if (udp->name == name) return true;
  }
  return false;
}

// The names of the cells `items` declares rather than instantiates: one
// declared directly among them, one inside a generate alternative, and one
// declared deeper still inside another such declaration. A cell declared this
// way travels inside the precompiled form of the cell that declares it, so an
// instance naming it already has something compiled to bind to and there is no
// separate entry to go looking for in any library.
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

// The loaded configuration of that name, or nullptr. A configuration is one of
// the design elements a library holds, so one reaches a bind the same way every
// other cell does: read back out of a compiled form.
const ConfigDecl* FindConfig(const CompilationUnit& unit,
                             std::string_view name) {
  for (const auto* cfg : unit.configs) {
    if (cfg->name == name) return cfg;
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
    // An instance names a cell, not a library, so the cell that answers to it
    // is looked for wherever it was compiled. Which library the design finally
    // binds it from is settled when the design is bound, not here.
    auto* child_decl = FindDescendableCell(unit_, {}, child.name);
    if (child_decl != nullptr) {
      descent.pending.push_back(child_decl);
    } else if (!HoldsPrimitive(unit_, child.name)) {
      // The instantiation is where the design asks for this cell, so that is
      // where the report about it stands.
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

  // The descent reaches the cells of a design in the order its own walk takes,
  // which is nothing the design states, so the report is put in name order: the
  // same design missing the same cells names them the same way however the walk
  // reached them.
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
    if (!descent.reached.insert(name).second) continue;
    auto* decl = FindDescendableCell(unit_, {}, name);
    if (decl == nullptr) {
      // A top-level cell is named to this tool rather than instantiated by
      // anything, so nothing written in a source description says where the
      // name came from and the report about it stands at no position.
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
      // The design statement is where this cell was asked for, so the report
      // about it stands at the cell name that statement wrote.
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
  return elab.Elaborate(top_names);
}

RtlirDesign* SeparateCompilationBinder::BindConfig(
    std::string_view config_name) {
  not_precompiled_.clear();

  const ConfigDecl* cfg = FindConfig(unit_, config_name);
  if (cfg == nullptr) {
    // The name is what this tool was invoked with in place of the names of the
    // top-level cells, and no source description reaches a bind, so there is
    // nothing written anywhere for this report to stand at.
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

  // The cells the design statement names root the design, so they are where
  // the check that everything below them was precompiled starts -- each taken
  // from the library the statement named for it, because a root of that name in
  // some other library heads a different hierarchy and would have the check
  // walk cells this design does not contain while missing ones it does.
  if (!DesignCellsPrecompiled(cfg)) return nullptr;

  Elaborator elab(arena_, diag_, &unit_);
  return elab.Elaborate(cfg);
}

}  // namespace delta
