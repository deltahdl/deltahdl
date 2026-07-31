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
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"
#include "parser/precompiled_library.h"

namespace delta {

namespace {

// The declaration named `name` among `decls`, or nullptr.
ModuleDecl* FindNamed(const std::vector<ModuleDecl*>& decls,
                      std::string_view name) {
  for (auto* decl : decls) {
    if (decl->name == name) return decl;
  }
  return nullptr;
}

// The declaration a descent continues into for the cell named `name`: the
// instantiable cell kinds whose bodies can hold further instances, every one
// of which a compiled form holds as a module declaration. Returns nullptr when
// no loaded cell of one of those kinds answers to the name.
ModuleDecl* FindDescendableCell(const CompilationUnit& unit,
                                std::string_view name) {
  if (auto* decl = FindNamed(unit.modules, name)) return decl;
  if (auto* decl = FindNamed(unit.interfaces, name)) return decl;
  if (auto* decl = FindNamed(unit.programs, name)) return decl;
  return FindNamed(unit.checkers, name);
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

}  // namespace

SeparateCompilationBinder::SeparateCompilationBinder(SourceManager& mgr,
                                                     Arena& arena,
                                                     DiagEngine& diag)
    : mgr_(mgr), arena_(arena), diag_(diag) {}

bool SeparateCompilationBinder::LoadLibrary(const std::filesystem::path& path) {
  if (PrecompiledLibrary::Load(path, unit_, mgr_, arena_, diag_)) return true;
  std::string where = path.string();
  diag_.Error({}, std::format("no cells read from library '{}'", where));
  return false;
}

void SeparateCompilationBinder::ReachSubinstances(const ModuleDecl* decl,
                                                  Descent& descent) {
  std::unordered_set<std::string_view> instantiated;
  CollectInstantiatedNames(decl->items, instantiated);
  std::unordered_set<std::string_view> declared_within;
  CollectNestedCellNames(decl->items, declared_within);
  for (auto child : instantiated) {
    if (declared_within.contains(child)) continue;
    if (!descent.reached.insert(child).second) continue;
    auto* child_decl = FindDescendableCell(unit_, child);
    if (child_decl != nullptr) {
      descent.pending.push_back(child_decl);
    } else if (!HoldsPrimitive(unit_, child)) {
      not_precompiled_.emplace_back(child);
    }
  }
}

bool SeparateCompilationBinder::AllCellsPrecompiled(
    const std::vector<std::string_view>& top_names) {
  Descent descent;
  for (auto name : top_names) {
    if (!descent.reached.insert(name).second) continue;
    auto* decl = FindDescendableCell(unit_, name);
    if (decl == nullptr) {
      not_precompiled_.emplace_back(name);
      continue;
    }
    descent.pending.push_back(decl);
  }

  while (!descent.pending.empty()) {
    const auto* decl = descent.pending.back();
    descent.pending.pop_back();
    ReachSubinstances(decl, descent);
  }

  // The descent reaches the cells of one declaration in no particular order,
  // so the report is put in name order: the same design missing the same cells
  // names them the same way every run.
  std::sort(not_precompiled_.begin(), not_precompiled_.end());
  for (const auto& name : not_precompiled_) {
    diag_.Error({}, std::format("cell '{}' was not precompiled", name));
  }
  return not_precompiled_.empty();
}

RtlirDesign* SeparateCompilationBinder::Bind(
    const std::vector<std::string_view>& top_names) {
  not_precompiled_.clear();
  if (!AllCellsPrecompiled(top_names)) return nullptr;

  Elaborator elab(arena_, diag_, &unit_);
  return elab.Elaborate(top_names);
}

}  // namespace delta
