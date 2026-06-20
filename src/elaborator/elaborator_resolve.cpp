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

  for (auto* pkg : unit_->packages) {
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
        auto val = ConstEvalInt(item->init_expr, cu_param_scope_);
        if (val) {
          auto* qname = arena_.Create<std::string>(
              std::string(pkg->name) + "." + std::string(item->name));
          cu_param_scope_[*qname] = *val;
        }
      }
    }
  }
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

void Elaborator::ResolveExternModules() {
  for (auto* mod : unit_->modules) {
    if (mod->is_extern) continue;

    ModuleDecl* extern_decl = nullptr;
    for (auto* other : unit_->modules) {
      if (other->is_extern && other->name == mod->name) {
        extern_decl = other;
        break;
      }
    }
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
    for (size_t i = 0; i < mod->ports.size(); ++i) {
      const PortDecl& ep = extern_decl->ports[i];
      const PortDecl& mp = mod->ports[i];
      if (!mp.name.empty() && !ep.name.empty() && mp.name != ep.name) {
        diag_.Error(mod->range.start,
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
      if (ep.direction != Direction::kNone &&
          mp.direction != Direction::kNone && ep.direction != mp.direction) {
        diag_.Error(
            mp.loc,
            std::format("module '{}' port '{}' direction does not match "
                        "extern declaration",
                        mod->name, mp.name));
        break;
      }
      if (ep.data_type.kind != DataTypeKind::kImplicit &&
          mp.data_type.kind != DataTypeKind::kImplicit &&
          !ExternPortTypesEquivalent(ep.data_type, mp.data_type)) {
        diag_.Error(mp.loc,
                    std::format("module '{}' port '{}' type does not match "
                                "extern declaration",
                                mod->name, mp.name));
        break;
      }
    }
    if (extern_decl->params.size() != mod->params.size()) {
      diag_.Error(mod->range.start,
                  std::format("module '{}' parameter count ({}) does not match "
                              "extern declaration ({})",
                              mod->name, mod->params.size(),
                              extern_decl->params.size()));
    } else {
      // The parameter lists must also correspond by name and position.
      for (size_t i = 0; i < mod->params.size(); ++i) {
        std::string_view mp_name = mod->params[i].first;
        std::string_view ep_name = extern_decl->params[i].first;
        if (!mp_name.empty() && !ep_name.empty() && mp_name != ep_name) {
          diag_.Error(mod->range.start,
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
          diag_.Error(mod->range.start,
                      std::format("module '{}' parameter '{}' at position {} "
                                  "does not match the parameter kind of the "
                                  "extern declaration",
                                  mod->name, mp_name, i));
          break;
        }
      }
    }
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
  bool applies = ov.src_lib.empty();
  if (!applies) {
    for (auto* mod : unit_->modules) {
      if (mod->name != name) continue;
      if (mod->library == ov.src_lib) {
        applies = true;
        break;
      }
    }
  }
  if (!applies) return std::nullopt;

  // An omitted target library is inherited from the parent cell (§33.4.1.6).
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  for (auto* mod : unit_->modules) {
    if (mod->is_extern) continue;
    if (mod->library == target_lib && mod->name == ov.use_cell) return mod;
  }
  return static_cast<ModuleDecl*>(nullptr);
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  if (!current_inst_path_.empty()) {
    for (const auto& [path, ulib, ucell] : instance_use_overrides_) {
      if (path != current_inst_path_) continue;
      if (name != ucell) continue;
      for (auto* mod : unit_->modules) {
        if (mod->is_extern) continue;
        if (mod->library == ulib && mod->name == ucell) return mod;
      }
      return nullptr;
    }
  }

  if (auto hit = ResolveCellUseOverride(name); hit.has_value()) {
    return *hit;
  }

  ModuleDecl* extern_decl = nullptr;
  std::vector<ModuleDecl*> candidates;
  for (auto* mod : unit_->modules) {
    if (mod->name != name) continue;
    if (mod->is_extern) {
      if (!extern_decl) extern_decl = mod;
    } else {
      candidates.push_back(mod);
    }
  }

  const std::vector<std::string>* override_liblist = nullptr;
  size_t best_match_len = 0;
  if (!current_inst_path_.empty()) {
    for (const auto& [rule_path, libs] : instance_liblist_overrides_) {
      bool matches = false;
      if (current_inst_path_ == rule_path) {
        matches = true;
      } else if (current_inst_path_.size() > rule_path.size() &&
                 current_inst_path_.compare(0, rule_path.size(), rule_path) ==
                     0 &&
                 current_inst_path_[rule_path.size()] == '.') {
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
    if (auto it = cell_clause_liblist_overrides_.find(std::string(name));
        it != cell_clause_liblist_overrides_.end()) {
      override_liblist = &it->second;
    }
  }

  if (override_liblist != nullptr && !candidates.empty()) {
    std::vector<ModuleDecl*> filtered;
    filtered.reserve(candidates.size());
    for (auto* c : candidates) {
      for (const auto& lib : *override_liblist) {
        if (lib == c->library) {
          filtered.push_back(c);
          break;
        }
      }
    }
    candidates = std::move(filtered);
    if (!candidates.empty()) {
      auto pri = [override_liblist](std::string_view lib) -> size_t {
        for (size_t i = 0; i < override_liblist->size(); ++i) {
          if ((*override_liblist)[i] == lib) return i;
        }
        return override_liblist->size();
      };
      ModuleDecl* best = candidates.front();
      size_t best_pri = pri(best->library);
      for (size_t i = 1; i < candidates.size(); ++i) {
        size_t p = pri(candidates[i]->library);
        if (p < best_pri) {
          best = candidates[i];
          best_pri = p;
        }
      }
      return best;
    }
  } else {
    // An empty selected library list selects no libraries to filter against;
    // it is treated below as no list being selected (§33.4.1.5).
    if (library_order_strict_ && !library_order_.empty() &&
        !candidates.empty()) {
      std::vector<ModuleDecl*> filtered;
      filtered.reserve(candidates.size());
      for (auto* c : candidates) {
        bool listed = false;
        for (const auto& lib : library_order_) {
          if (lib == c->library) {
            listed = true;
            break;
          }
        }
        if (listed) filtered.push_back(c);
      }
      candidates = std::move(filtered);
    }
    if (!candidates.empty()) {
      // §33.4.1.5: when no library list clause is selected (or the selected
      // list is empty), the list holds only the parent cell's library, so an
      // instance binds to the cell defined in its parent's library.
      bool no_list_selected = !library_order_strict_ || library_order_.empty();
      if (in_config_elaboration_ && no_list_selected &&
          !current_library_.empty()) {
        for (auto* c : candidates) {
          if (c->library == current_library_) return c;
        }
      }
      auto priority = [this](std::string_view lib) -> size_t {
        for (size_t i = 0; i < library_order_.size(); ++i) {
          if (library_order_[i] == lib) return i;
        }
        return library_order_.size();
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
  }
  if (extern_decl) return extern_decl;

  auto pit = std::find_if(unit_->programs.begin(), unit_->programs.end(),
                          [name](auto* p) { return p->name == name; });
  if (pit != unit_->programs.end()) return *pit;

  auto iit = std::find_if(unit_->interfaces.begin(), unit_->interfaces.end(),
                          [name](auto* i) { return i->name == name; });
  if (iit != unit_->interfaces.end()) return *iit;

  auto cit = std::find_if(unit_->checkers.begin(), unit_->checkers.end(),
                          [name](auto* c) { return c->name == name; });
  if (cit != unit_->checkers.end()) return *cit;

  return nullptr;
}

ModuleDecl* Elaborator::FindModuleInScope(std::string_view name) const {
  auto it = nested_module_decls_.find(name);
  if (it != nested_module_decls_.end()) return it->second;
  return FindModule(name);
}

}  // namespace delta
