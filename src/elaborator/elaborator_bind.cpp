#include <algorithm>
#include <format>
#include <functional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static bool IsBindTargetScope(std::string_view target,
                              const CompilationUnit* unit) {
  if (target.find('.') != std::string_view::npos) return false;
  for (auto* m : unit->modules)
    if (m->name == target) return true;
  for (auto* i : unit->interfaces)
    if (i->name == target) return true;
  for (auto* c : unit->checkers)
    if (c->name == target) return true;
  for (auto* p : unit->programs)
    if (p->name == target) return true;
  return false;
}

static std::unordered_set<std::string_view> CollectDeclaredNames(
    const RtlirModule* mod) {
  std::unordered_set<std::string_view> names;
  for (const auto& v : mod->variables) names.insert(v.name);
  for (const auto& n : mod->nets) names.insert(n.name);
  for (const auto& p : mod->ports) names.insert(p.name);
  for (const auto& c : mod->children) {
    if (!c.inst_name.empty()) names.insert(c.inst_name);
  }
  return names;
}

void Elaborator::ApplyBindDirectives(RtlirModule* top) {
  if (!top) return;
  std::vector<BindDirective*> binds;
  for (auto* bd : unit_->bind_directives) binds.push_back(bd);
  for (auto* m : unit_->modules)
    for (auto* bd : m->bind_directives) binds.push_back(bd);
  for (auto* i : unit_->interfaces)
    for (auto* bd : i->bind_directives) binds.push_back(bd);
  for (auto* p : unit_->programs)
    for (auto* bd : p->bind_directives) binds.push_back(bd);
  if (binds.empty()) return;
  std::unordered_set<RtlirModule*> visited;
  std::unordered_set<BindDirective*> applied;
  WalkForBind(top, std::string(top->name), binds, false, visited, applied);

  // §23.11: the bind_target_scope shall be a module or an interface, and a
  // bind_target_instance shall be an instance of a module or an interface. A
  // target naming a known scope is honored designwide even when that scope is
  // never instantiated, but a target that resolves to neither a known scope
  // nor any instance in the hierarchy denotes nothing bindable and is an error.
  for (auto* bd : binds) {
    if (applied.count(bd)) continue;
    if (IsBindTargetScope(bd->target, unit_)) continue;
    diag_.Error(bd->loc,
                std::format("bind target '{}' is neither a module or interface "
                            "scope nor an instance",
                            bd->target));
  }
}

void Elaborator::WalkForBind(RtlirModule* mod, const std::string& hier_path,
                             const std::vector<BindDirective*>& binds,
                             bool under_bind,
                             std::unordered_set<RtlirModule*>& visited,
                             std::unordered_set<BindDirective*>& applied) {
  if (!mod) return;
  if (!visited.insert(mod).second) return;

  for (auto* bd : binds) {
    bool applies = false;
    bool has_instances = !bd->target_instances.empty();
    bool is_scope = IsBindTargetScope(bd->target, unit_);
    if (is_scope && !has_instances) {
      if (mod->name == bd->target) applies = true;
    } else if (is_scope && has_instances) {
      if (mod->name == bd->target) {
        for (auto inst_path : bd->target_instances) {
          if (hier_path == inst_path) {
            applies = true;
            break;
          }
        }
      }
    } else {
      if (hier_path == bd->target) applies = true;
    }
    if (!applies) continue;
    // The target resolved to a real scope or instance, so it is bindable even
    // if elaboration of the instantiation later reports a different error.
    applied.insert(bd);
    if (under_bind) {
      diag_.Error(bd->loc,
                  "bind target shall not be a scope created by a bind");
      continue;
    }
    ApplyBindInstance(bd, mod);
  }

  size_t n = mod->children.size();
  for (size_t i = 0; i < n; ++i) {
    auto& c = mod->children[i];
    if (!c.resolved) continue;
    bool child_under_bind = under_bind || c.is_bound;
    std::string child_path = hier_path;
    child_path.push_back('.');
    child_path.append(c.inst_name.data(), c.inst_name.size());
    WalkForBind(c.resolved, child_path, binds, child_under_bind, visited,
                applied);
  }
}

void Elaborator::ApplyBindInstance(BindDirective* bd, RtlirModule* target) {
  auto* item = bd->instantiation;
  if (!item) return;

  auto* target_decl = FindModule(target->name);
  if (target_decl && target_decl->decl_kind == ModuleDeclKind::kInterface) {
    auto* bound_decl = FindModule(item->inst_module);
    if (bound_decl && bound_decl->decl_kind != ModuleDeclKind::kInterface &&
        bound_decl->decl_kind != ModuleDeclKind::kChecker) {
      diag_.Error(bd->loc,
                  std::format("cannot bind non-interface/non-checker '{}' "
                              "into interface '{}'",
                              item->inst_module, target->name));
      return;
    }
  }

  auto declared = CollectDeclaredNames(target);
  if (!item->inst_name.empty() && declared.count(item->inst_name)) {
    diag_.Error(bd->loc, std::format("bind instance name '{}' clashes with "
                                     "existing name in target scope '{}'",
                                     item->inst_name, target->name));
    return;
  }

  auto* child_decl = FindModule(item->inst_module);
  if (!child_decl) {
    diag_.Error(bd->loc, std::format("bind refers to unknown module '{}'",
                                     item->inst_module));
    return;
  }

  for (const auto& [pname, conn_expr] : item->inst_ports) {
    if (!conn_expr || conn_expr->kind != ExprKind::kIdentifier) continue;
    auto name = conn_expr->text;
    bool found = false;
    for (const auto& v : target->variables) {
      if (v.name == name) {
        found = true;
        break;
      }
    }
    if (!found) {
      for (const auto& n : target->nets) {
        if (n.name == name) {
          found = true;
          break;
        }
      }
    }
    if (!found) {
      for (const auto& p : target->ports) {
        if (p.name == name) {
          found = true;
          break;
        }
      }
    }
    if (!found) {
      diag_.Error(bd->loc,
                  std::format("bind port connection '{}' references "
                              "undeclared signal '{}' in target scope '{}'",
                              pname, name, target->name));
      return;
    }
  }

  ParamList empty_params;
  auto* resolved = ElaborateModule(child_decl, empty_params);
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;
  inst.resolved = resolved;
  inst.is_bound = true;

  if (resolved) {
    const auto& child_ports = resolved->ports;
    const bool kIsOrdered =
        !item->inst_ports.empty() && item->inst_ports[0].first.empty();
    for (size_t i = 0; i < item->inst_ports.size(); ++i) {
      auto& [port_name, conn_expr] = item->inst_ports[i];
      RtlirPortBinding binding;
      binding.connection = conn_expr;
      auto it = child_ports.end();
      if (kIsOrdered) {
        if (i < child_ports.size()) {
          it = child_ports.begin() + static_cast<ptrdiff_t>(i);
          binding.port_name = it->name;
        }
      } else {
        binding.port_name = port_name;
        it = std::find_if(
            child_ports.begin(), child_ports.end(),
            [&](const RtlirPort& p) { return p.name == port_name; });
      }
      if (it != child_ports.end()) {
        binding.direction = it->direction;
        binding.width = it->width;
      } else {
        binding.direction = Direction::kInput;
        binding.width = 1;
      }
      inst.port_bindings.push_back(binding);
    }
  }

  target->children.push_back(inst);
}

namespace {

struct ExportKey {
  std::string_view iface_inst;
  std::string_view modport;
  std::string_view name;
  bool operator==(const ExportKey& o) const {
    return iface_inst == o.iface_inst && modport == o.modport && name == o.name;
  }
};

struct ExportKeyHash {
  size_t operator()(const ExportKey& k) const {
    std::hash<std::string_view> h;
    return h(k.iface_inst) ^ (h(k.modport) << 1) ^ (h(k.name) << 2);
  }
};

struct ExportSite {
  std::string_view child_inst;
  bool is_task = false;
  SourceLoc loc;
};

const ModportDecl* FindModportInInterface(const ModuleDecl* iface,
                                          std::string_view name) {
  for (const auto* mp : iface->modports) {
    if (mp->name == name) return mp;
  }
  return nullptr;
}

const ModuleItem* FindInterfaceExternPrototype(const ModuleDecl* iface,
                                               std::string_view name) {
  for (const auto* item : iface->items) {
    if (!item->is_extern) continue;
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl)
      continue;
    if (item->name == name) return item;
  }
  return nullptr;
}

const ModuleItem* FindOutOfBlockBodyInChild(const ModuleDecl* child,
                                            std::string_view iface_port_name,
                                            std::string_view method_name) {
  for (const auto* item : child->items) {
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl)
      continue;
    if (item->method_class == iface_port_name && item->name == method_name)
      return item;
  }
  return nullptr;
}

// §25.7: when a modport exports a subroutine using a full prototype, the
// definition supplied by the connected module shall match that prototype
// exactly — same kind (task vs function), the same argument types and
// directions, and, for a function, the same return type.
bool ExportPrototypeMatchesBody(const ModuleItem* proto,
                                const ModuleItem* body) {
  if (proto->kind != body->kind) return false;
  if (proto->func_args.size() != body->func_args.size()) return false;
  for (size_t i = 0; i < proto->func_args.size(); ++i) {
    if (!TypesMatch(proto->func_args[i].data_type,
                    body->func_args[i].data_type))
      return false;
    if (proto->func_args[i].direction != body->func_args[i].direction)
      return false;
  }
  // A modport function prototype keeps its return type in `data_type`, while an
  // out-of-block body keeps it in `return_type`; compare the matching fields.
  return !(proto->kind == ModuleItemKind::kFunctionDecl &&
           !TypesMatch(proto->data_type, body->return_type));
}

}  // namespace

void Elaborator::ValidateModportExportConflicts(RtlirModule* top) {
  if (!top) return;
  std::unordered_set<RtlirModule*> visited;
  WalkForExportConflicts(top, visited);
}

void Elaborator::WalkForExportConflicts(
    RtlirModule* mod, std::unordered_set<RtlirModule*>& visited) {
  if (!mod) return;
  if (!visited.insert(mod).second) return;

  std::unordered_map<std::string_view, std::string_view> iface_inst_to_type;
  for (const auto& c : mod->children) {
    if (auto* cd = FindModule(c.module_name);
        cd && cd->decl_kind == ModuleDeclKind::kInterface) {
      iface_inst_to_type[c.inst_name] = c.module_name;
    }
  }

  std::unordered_map<ExportKey, std::vector<ExportSite>, ExportKeyHash> buckets;

  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto* child_decl = FindModule(child.module_name);
    if (!child_decl) continue;
    if (child_decl->decl_kind == ModuleDeclKind::kInterface) continue;

    for (const auto& binding : child.port_bindings) {
      if (!binding.connection) continue;
      const auto* conn = binding.connection;

      std::string_view iface_inst_name;
      std::string_view modport_name;
      if (conn->kind == ExprKind::kIdentifier) {
        iface_inst_name = conn->text;
      } else if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
                 conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
                 conn->rhs->kind == ExprKind::kIdentifier) {
        iface_inst_name = conn->lhs->text;
        modport_name = conn->rhs->text;
      } else {
        continue;
      }

      auto it = iface_inst_to_type.find(iface_inst_name);
      if (it == iface_inst_to_type.end()) continue;

      auto* iface_decl = FindModule(it->second);
      if (!iface_decl) continue;

      auto collect_exports = [&](const std::vector<ModportPort>& mp_ports) {
        for (const auto& pp : mp_ports) {
          if (!pp.is_export) continue;
          if (pp.name.empty()) continue;
          const auto* body =
              FindOutOfBlockBodyInChild(child_decl, binding.port_name, pp.name);
          if (!body) continue;
          // §25.7: an export written as a full prototype pins the signature
          // the defining module must provide; a definition that does not
          // match it exactly is an elaboration error.
          if (pp.prototype && !ExportPrototypeMatchesBody(pp.prototype, body)) {
            diag_.Error(
                body->loc,
                std::format(
                    "definition of exported subroutine '{}' in module '{}' "
                    "does not match the prototype declared in the modport",
                    pp.name, child.module_name));
          }
          ExportKey key{iface_inst_name, modport_name, pp.name};
          ExportSite site;
          site.child_inst = child.inst_name;
          site.is_task = body->kind == ModuleItemKind::kTaskDecl;
          site.loc = body->loc;
          buckets[key].push_back(site);
        }
      };

      if (!modport_name.empty()) {
        const auto* mp = FindModportInInterface(iface_decl, modport_name);
        if (!mp) continue;
        collect_exports(mp->ports);
      } else {
        for (const auto* mp : iface_decl->modports) {
          collect_exports(mp->ports);
        }
      }
    }
  }

  for (const auto& [key, sites] : buckets) {
    if (sites.size() < 2) continue;

    auto type_it = iface_inst_to_type.find(key.iface_inst);
    if (type_it == iface_inst_to_type.end()) continue;
    auto* iface_decl = FindModule(type_it->second);
    if (!iface_decl) continue;

    const ModuleItem* prototype =
        FindInterfaceExternPrototype(iface_decl, key.name);
    bool is_task_export = sites[0].is_task;
    bool is_forkjoin_task = prototype && prototype->is_extern &&
                            prototype->is_forkjoin &&
                            prototype->kind == ModuleItemKind::kTaskDecl;

    if (is_task_export && is_forkjoin_task) continue;

    if (!is_task_export) {
      diag_.Error(sites[0].loc,
                  std::format("function '{}' exported by more than one module "
                              "connected to interface instance '{}' (§25.7.4: "
                              "multiple export of functions is not allowed)",
                              key.name, key.iface_inst));
    } else {
      diag_.Error(
          sites[0].loc,
          std::format("task '{}' exported by more than one module connected "
                      "to interface instance '{}' (§25.7.4: declare the task "
                      "as `extern forkjoin` in the interface to allow "
                      "multiple exports)",
                      key.name, key.iface_inst));
    }
  }

  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    WalkForExportConflicts(child.resolved, visited);
  }
}

}  // namespace delta
