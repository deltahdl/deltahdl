#include <algorithm>
#include <format>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §33.4.1.4: a library-qualified cell clause applies only when a cell of the
// given name is actually defined in that library; an unqualified clause (empty
// src_lib) always applies.
bool CellUseOverrideApplies(std::string_view src_lib, std::string_view name,
                            CompilationUnit* unit) {
  if (src_lib.empty()) return true;
  for (auto* mod : unit->modules) {
    if (mod->name != name) continue;
    if (mod->library == src_lib) return true;
  }
  return false;
}

// Returns the non-extern module named use_cell defined in target_lib, or
// nullptr when no such cell exists.
ModuleDecl* FindCellInLibrary(std::string_view target_lib,
                              std::string_view use_cell,
                              CompilationUnit* unit) {
  for (auto* mod : unit->modules) {
    if (mod->is_extern) continue;
    if (mod->library == target_lib && mod->name == use_cell) return mod;
  }
  return nullptr;
}

// §33.4.1.3: when the instance currently being elaborated has an explicit use
// clause naming this cell, it binds the named cell. Returns nullopt when no
// instance use override applies (so normal resolution should continue), or the
// override result (which may be nullptr if the named cell does not exist).
std::optional<ModuleDecl*> FindInstanceUseOverride(
    const std::string& current_inst_path, std::string_view name,
    const std::vector<std::tuple<std::string, std::string, std::string>>&
        instance_use_overrides,
    CompilationUnit* unit) {
  if (current_inst_path.empty()) return std::nullopt;
  for (const auto& [path, ulib, ucell] : instance_use_overrides) {
    if (path != current_inst_path) continue;
    if (name != ucell) continue;
    return FindCellInLibrary(ulib, ucell, unit);
  }
  return std::nullopt;
}

// Partitions modules named `name` into the non-extern candidates and the first
// extern declaration encountered.
void CollectModuleCandidates(std::string_view name, CompilationUnit* unit,
                             std::vector<ModuleDecl*>& candidates,
                             ModuleDecl*& extern_decl) {
  for (auto* mod : unit->modules) {
    if (mod->name != name) continue;
    if (mod->is_extern) {
      if (!extern_decl) extern_decl = mod;
    } else {
      candidates.push_back(mod);
    }
  }
}

// Returns the candidates whose library appears in `liblist`, preserving order.
std::vector<ModuleDecl*> FilterCandidatesByLibrary(
    const std::vector<ModuleDecl*>& candidates,
    const std::vector<std::string>& liblist) {
  std::vector<ModuleDecl*> filtered;
  filtered.reserve(candidates.size());
  for (auto* c : candidates) {
    for (const auto& lib : liblist) {
      if (lib == c->library) {
        filtered.push_back(c);
        break;
      }
    }
  }
  return filtered;
}

// Selects the candidate whose library ranks earliest in `order` (libraries not
// listed rank last). On ties the earlier candidate wins. `candidates` must be
// non-empty.
ModuleDecl* PickByLibraryOrder(const std::vector<ModuleDecl*>& candidates,
                               const std::vector<std::string>& order) {
  auto priority = [&order](std::string_view lib) -> size_t {
    for (size_t i = 0; i < order.size(); ++i) {
      if (order[i] == lib) return i;
    }
    return order.size();
  };
  ModuleDecl* best = candidates.front();
  size_t best_pri = priority(best->library);
  for (size_t i = 1; i < candidates.size(); ++i) {
    size_t pri = priority(candidates[i]->library);
    if (pri < best_pri) {
      best = candidates[i];
      best_pri = pri;
    }
  }
  return best;
}

// Resolves `name` to a program, interface, or checker (in that order) when no
// module matched, returning nullptr if none exists.
ModuleDecl* FindNonModuleDesign(std::string_view name, CompilationUnit* unit) {
  auto pit = std::find_if(unit->programs.begin(), unit->programs.end(),
                          [name](auto* p) { return p->name == name; });
  if (pit != unit->programs.end()) return *pit;

  auto iit = std::find_if(unit->interfaces.begin(), unit->interfaces.end(),
                          [name](auto* i) { return i->name == name; });
  if (iit != unit->interfaces.end()) return *iit;

  auto cit = std::find_if(unit->checkers.begin(), unit->checkers.end(),
                          [name](auto* c) { return c->name == name; });
  if (cit != unit->checkers.end()) return *cit;

  return nullptr;
}

// Records each package's value parameters in the compilation-unit parameter
// scope under their fully qualified "package.name" key (§26.3).
void RegisterPackageParams(CompilationUnit* unit, ScopeMap& cu_param_scope,
                           Arena& arena) {
  for (auto* pkg : unit->packages) {
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
        auto val = ConstEvalInt(item->init_expr, cu_param_scope);
        if (val) {
          auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                                  std::string(item->name));
          cu_param_scope[*qname] = *val;
        }
      }
    }
  }
}

}  // namespace

void Elaborator::RegisterCuScopeItems() {
  class_names_.insert("semaphore");

  class_names_.insert("mailbox");

  class_names_.insert("weak_reference");

  class_names_.insert("process");
  for (auto* item : unit_->cu_items) {
    if (!item->name.empty()) cu_scope_names_.insert(item->name);
    if (item->kind == ModuleItemKind::kTypedef) {
      typedefs_[item->name] = item->typedef_type;
    } else if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      class_names_.insert(item->class_decl->name);
      if (!item->class_decl->params.empty())
        parameterized_class_names_.insert(item->class_decl->name);
    } else if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      auto val = ConstEvalInt(item->init_expr, cu_param_scope_);
      if (val) {
        cu_param_scope_[item->name] = *val;
      }
    }
  }
  for (auto* cls : unit_->classes) {
    class_names_.insert(cls->name);
    cu_scope_names_.insert(cls->name);
    if (!cls->params.empty()) parameterized_class_names_.insert(cls->name);
  }

  RegisterPackageParams(unit_, cu_param_scope_, arena_);
}

ModuleItem* Elaborator::FindCuScopeItem(std::string_view name) const {
  for (auto* item : unit_->cu_items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

// Two port data types correspond for extern-declaration matching when they
// share a base kind, signedness, and (for named types) the same type name.
// Packed/unpacked dimension sizes are parameter-dependent expressions that are
// not yet evaluated here, so only the dimension-independent attributes that the
// parser records are compared.
static bool ExternPortTypesEquivalent(const DataType& a, const DataType& b) {
  return a.kind == b.kind && a.is_signed == b.is_signed &&
         a.type_name == b.type_name;
}

// Returns the matching extern declaration for an actual module, or nullptr.
static ModuleDecl* FindExternDeclFor(const ModuleDecl* mod,
                                     CompilationUnit* unit) {
  for (auto* other : unit->modules) {
    if (other->is_extern && other->name == mod->name) return other;
  }
  return nullptr;
}

// §23.5: checks that each port of the actual module corresponds to the extern
// declaration in name, direction, and (when both sides state it) type. Reports
// the first mismatch found.
static void CheckExternPortMatch(const ModuleDecl* mod,
                                 const ModuleDecl* extern_decl,
                                 DiagEngine& diag) {
  for (size_t i = 0; i < mod->ports.size(); ++i) {
    const PortDecl& ep = extern_decl->ports[i];
    const PortDecl& mp = mod->ports[i];
    if (!mp.name.empty() && !ep.name.empty() && mp.name != ep.name) {
      diag.Error(mod->range.start,
                 std::format("module '{}' port '{}' at position {} does not "
                             "match extern declaration port '{}'",
                             mod->name, mp.name, i, ep.name));
      break;
    }
    // §23.5 requires the extern declaration to match the actual module in the
    // equivalent types of corresponding ports. Direction and data type are
    // only compared when the extern header states them: a non-ANSI extern
    // port list supplies names and positions alone and leaves the type to the
    // actual definition, so an unspecified side is treated as a match.
    if (ep.direction != Direction::kNone && mp.direction != Direction::kNone &&
        ep.direction != mp.direction) {
      diag.Error(mp.loc,
                 std::format("module '{}' port '{}' direction does not match "
                             "extern declaration",
                             mod->name, mp.name));
      break;
    }
    if (ep.data_type.kind != DataTypeKind::kImplicit &&
        mp.data_type.kind != DataTypeKind::kImplicit &&
        !ExternPortTypesEquivalent(ep.data_type, mp.data_type)) {
      diag.Error(mp.loc,
                 std::format("module '{}' port '{}' type does not match "
                             "extern declaration",
                             mod->name, mp.name));
      break;
    }
  }
}

// §23.5: checks the parameter list of the actual module against the extern
// declaration by name, position, and parameter kind (type vs. value). Reports
// the first mismatch found.
static void CheckExternParamMatch(const ModuleDecl* mod,
                                  const ModuleDecl* extern_decl,
                                  DiagEngine& diag) {
  if (extern_decl->params.size() != mod->params.size()) {
    diag.Error(
        mod->range.start,
        std::format("module '{}' parameter count ({}) does not match "
                    "extern declaration ({})",
                    mod->name, mod->params.size(), extern_decl->params.size()));
    return;
  }
  // The parameter lists must also correspond by name and position.
  for (size_t i = 0; i < mod->params.size(); ++i) {
    std::string_view mp_name = mod->params[i].first;
    std::string_view ep_name = extern_decl->params[i].first;
    if (!mp_name.empty() && !ep_name.empty() && mp_name != ep_name) {
      diag.Error(mod->range.start,
                 std::format("module '{}' parameter '{}' at position {} "
                             "does not match extern declaration "
                             "parameter '{}'",
                             mod->name, mp_name, i, ep_name));
      break;
    }
    // §23.5 also calls for equivalent parameter types. A type parameter and
    // a value parameter at the same position are not equivalent, so the
    // two declarations must agree on whether each entry is a type
    // parameter.
    bool mp_is_type = mod->type_param_names.count(mp_name) != 0;
    bool ep_is_type = extern_decl->type_param_names.count(ep_name) != 0;
    if (mp_is_type != ep_is_type) {
      diag.Error(mod->range.start,
                 std::format("module '{}' parameter '{}' at position {} "
                             "does not match the parameter kind of the "
                             "extern declaration",
                             mod->name, mp_name, i));
      break;
    }
  }
}

void Elaborator::ResolveExternModules() {
  for (auto* mod : unit_->modules) {
    if (mod->is_extern) continue;

    ModuleDecl* extern_decl = FindExternDeclFor(mod, unit_);
    if (!extern_decl) continue;

    if (mod->has_wildcard_ports) {
      mod->ports = extern_decl->ports;
      if (mod->params.empty() && !extern_decl->params.empty()) {
        mod->params = extern_decl->params;
        mod->type_param_names = extern_decl->type_param_names;
        mod->has_param_port_list = extern_decl->has_param_port_list;
      }
      continue;
    }

    if (extern_decl->ports.size() != mod->ports.size()) {
      diag_.Error(
          mod->range.start,
          std::format("module '{}' port count ({}) does not match "
                      "extern declaration ({})",
                      mod->name, mod->ports.size(), extern_decl->ports.size()));
      continue;
    }
    CheckExternPortMatch(mod, extern_decl, diag_);
    CheckExternParamMatch(mod, extern_decl, diag_);
  }
}

std::optional<ModuleDecl*> Elaborator::ResolveCellUseOverride(
    std::string_view name) const {
  auto it = cell_clause_use_overrides_.find(std::string(name));
  if (it == cell_clause_use_overrides_.end()) return std::nullopt;
  const auto& ov = it->second;

  // A library-qualified cell clause applies only to the cell as defined in
  // that library (§33.4.1.4); if no such cell exists the clause matches
  // nothing and resolution proceeds normally.
  if (!CellUseOverrideApplies(ov.src_lib, name, unit_)) return std::nullopt;

  // An omitted target library is inherited from the parent cell (§33.4.1.6).
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  return FindCellInLibrary(target_lib, ov.use_cell, unit_);
}

// §33.4.1.4, §33.4.1.5: selects the library list that governs resolution of
// `name`, preferring the most specific instance-scoped liblist rule and falling
// back to a cell-clause liblist. Returns nullptr when no liblist clause
// applies.
static const std::vector<std::string>* SelectOverrideLiblist(
    std::string_view name, const std::string& current_inst_path,
    const std::vector<std::pair<std::string, std::vector<std::string>>>&
        instance_liblist_overrides,
    const std::unordered_map<std::string, std::vector<std::string>>&
        cell_clause_liblist_overrides) {
  const std::vector<std::string>* override_liblist = nullptr;
  size_t best_match_len = 0;
  if (!current_inst_path.empty()) {
    for (const auto& [rule_path, libs] : instance_liblist_overrides) {
      bool matches = false;
      if (current_inst_path == rule_path) {
        matches = true;
      } else if (current_inst_path.size() > rule_path.size() &&
                 current_inst_path.compare(0, rule_path.size(), rule_path) ==
                     0 &&
                 current_inst_path[rule_path.size()] == '.') {
        matches = true;
      }
      if (matches && rule_path.size() >= best_match_len) {
        override_liblist = &libs;
        best_match_len = rule_path.size();
      }
    }
  }

  // Absent an instance-scoped library list, a cell selection clause may name
  // the library list for this cell (§33.4.1.4, §33.4.1.5).
  if (override_liblist == nullptr) {
    if (auto it = cell_clause_liblist_overrides.find(std::string(name));
        it != cell_clause_liblist_overrides.end()) {
      override_liblist = &it->second;
    }
  }
  return override_liblist;
}

// Chooses among `candidates` using the global library order, applying strict
// library-order filtering and the config-elaboration parent-library preference
// (§33.4.1.5). Returns nullptr when no candidate survives filtering.
static ModuleDecl* PickCandidateByGlobalOrder(
    std::vector<ModuleDecl*> candidates,
    const std::vector<std::string>& library_order, bool library_order_strict,
    bool in_config_elaboration, std::string_view current_library) {
  // An empty selected library list selects no libraries to filter against;
  // it is treated here as no list being selected (§33.4.1.5).
  if (library_order_strict && !library_order.empty() && !candidates.empty()) {
    candidates = FilterCandidatesByLibrary(candidates, library_order);
  }
  if (candidates.empty()) return nullptr;

  // §33.4.1.5: when no library list clause is selected (or the selected
  // list is empty), the list holds only the parent cell's library, so an
  // instance binds to the cell defined in its parent's library.
  bool no_list_selected = !library_order_strict || library_order.empty();
  if (in_config_elaboration && no_list_selected && !current_library.empty()) {
    for (auto* c : candidates) {
      if (c->library == current_library) return c;
    }
  }
  return PickByLibraryOrder(candidates, library_order);
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  if (auto hit = FindInstanceUseOverride(current_inst_path_, name,
                                         instance_use_overrides_, unit_);
      hit.has_value()) {
    return *hit;
  }

  if (auto hit = ResolveCellUseOverride(name); hit.has_value()) {
    return *hit;
  }

  ModuleDecl* extern_decl = nullptr;
  std::vector<ModuleDecl*> candidates;
  CollectModuleCandidates(name, unit_, candidates, extern_decl);

  const std::vector<std::string>* override_liblist = SelectOverrideLiblist(
      name, current_inst_path_, instance_liblist_overrides_,
      cell_clause_liblist_overrides_);

  if (override_liblist != nullptr && !candidates.empty()) {
    candidates = FilterCandidatesByLibrary(candidates, *override_liblist);
    if (!candidates.empty()) {
      return PickByLibraryOrder(candidates, *override_liblist);
    }
  } else {
    if (ModuleDecl* picked = PickCandidateByGlobalOrder(
            std::move(candidates), library_order_, library_order_strict_,
            in_config_elaboration_, current_library_)) {
      return picked;
    }
  }
  if (extern_decl) return extern_decl;

  return FindNonModuleDesign(name, unit_);
}

ModuleDecl* Elaborator::FindModuleInScope(std::string_view name) const {
  auto it = nested_module_decls_.find(name);
  if (it != nested_module_decls_.end()) return it->second;
  return FindModule(name);
}

}  // namespace delta
