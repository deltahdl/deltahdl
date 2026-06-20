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

static std::vector<BindDirective*> CollectBindDirectives(
    const CompilationUnit* unit) {
  std::vector<BindDirective*> binds;
  binds.reserve(unit->bind_directives.size());
  for (auto* bd : unit->bind_directives) binds.push_back(bd);
  for (auto* m : unit->modules)
    for (auto* bd : m->bind_directives) binds.push_back(bd);
  for (auto* i : unit->interfaces)
    for (auto* bd : i->bind_directives) binds.push_back(bd);
  for (auto* p : unit->programs)
    for (auto* bd : p->bind_directives) binds.push_back(bd);
  return binds;
}

// §23.11: the bind_target_scope shall be a module or an interface, and a
// bind_target_instance shall be an instance of a module or an interface. A
// target naming a known scope is honored designwide even when that scope is
// never instantiated, but a target that resolves to neither a known scope
// nor any instance in the hierarchy denotes nothing bindable and is an error.
static void ReportUnmatchedBindTargets(
    const std::vector<BindDirective*>& binds,
    const std::unordered_set<BindDirective*>& applied,
    const CompilationUnit* unit, DiagEngine& diag) {
  for (auto* bd : binds) {
    if (applied.count(bd)) continue;
    if (IsBindTargetScope(bd->target, unit)) continue;
    diag.Error(bd->loc,
               std::format("bind target '{}' is neither a module or interface "
                           "scope nor an instance",
                           bd->target));
  }
}

void Elaborator::ApplyBindDirectives(RtlirModule* top) {
  if (!top) return;
  std::vector<BindDirective*> binds = CollectBindDirectives(unit_);
  if (binds.empty()) return;
  std::unordered_set<RtlirModule*> visited;
  std::unordered_set<BindDirective*> applied;
  BindWalkCtx ctx{binds, visited, applied};
  WalkForBind(top, std::string(top->name), false, ctx);

  ReportUnmatchedBindTargets(binds, applied, unit_, diag_);
}

static bool BindAppliesToModule(const BindDirective* bd, const RtlirModule* mod,
                                const std::string& hier_path,
                                const CompilationUnit* unit) {
  bool has_instances = !bd->target_instances.empty();
  bool is_scope = IsBindTargetScope(bd->target, unit);
  if (is_scope && !has_instances) {
    return mod->name == bd->target;
  }
  if (is_scope && has_instances) {
    if (mod->name != bd->target) return false;
    for (auto inst_path : bd->target_instances) {
      if (hier_path == inst_path) return true;
    }
    return false;
  }
  return hier_path == bd->target;
}

// Build the dotted hierarchical path of a child instance from its parent path.
static std::string BindChildPath(const std::string& hier_path,
                                 std::string_view inst_name) {
  std::string child_path = hier_path;
  child_path.push_back('.');
  child_path.append(inst_name.data(), inst_name.size());
  return child_path;
}

void Elaborator::WalkForBind(RtlirModule* mod, const std::string& hier_path,
                             bool under_bind, BindWalkCtx& ctx) {
  if (!mod) return;
  if (!ctx.visited.insert(mod).second) return;

  for (auto* bd : ctx.binds) {
    if (!BindAppliesToModule(bd, mod, hier_path, unit_)) continue;
    // The target resolved to a real scope or instance, so it is bindable even
    // if elaboration of the instantiation later reports a different error.
    ctx.applied.insert(bd);
    if (under_bind) {
      diag_.Error(bd->loc,
                  "bind target shall not be a scope created by a bind");
      continue;
    }
    ApplyBindInstance(bd, mod);
  }

  for (auto& c : mod->children) {
    if (!c.resolved) continue;
    bool child_under_bind = under_bind || c.is_bound;
    WalkForBind(c.resolved, BindChildPath(hier_path, c.inst_name),
                child_under_bind, ctx);
  }
}

static bool TargetHasSignal(const RtlirModule* target, std::string_view name) {
  for (const auto& v : target->variables)
    if (v.name == name) return true;
  for (const auto& n : target->nets)
    if (n.name == name) return true;
  for (const auto& p : target->ports)
    if (p.name == name) return true;
  return false;
}

// Every identifier port connection in the bind instantiation must name a signal
// declared in the target scope. Returns false (after reporting) on the first
// connection that refers to an undeclared signal.
static bool ValidateBindPortConnections(const BindDirective* bd,
                                        const ModuleItem* item,
                                        const RtlirModule* target,
                                        DiagEngine& diag) {
  for (const auto& [pname, conn_expr] : item->inst_ports) {
    if (!conn_expr || conn_expr->kind != ExprKind::kIdentifier) continue;
    auto name = conn_expr->text;
    if (!TargetHasSignal(target, name)) {
      diag.Error(bd->loc,
                 std::format("bind port connection '{}' references "
                             "undeclared signal '{}' in target scope '{}'",
                             pname, name, target->name));
      return false;
    }
  }
  return true;
}

static void BuildBoundPortBindings(const ModuleItem* item,
                                   const RtlirModule* resolved,
                                   RtlirModuleInst& inst) {
  const auto& child_ports = resolved->ports;
  const bool kIsOrdered =
      !item->inst_ports.empty() && item->inst_ports[0].first.empty();
  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    const auto& [port_name, conn_expr] = item->inst_ports[i];
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
      it =
          std::find_if(child_ports.begin(), child_ports.end(),
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

  if (!ValidateBindPortConnections(bd, item, target, diag_)) return;

  ParamList empty_params;
  auto* resolved = ElaborateModule(child_decl, empty_params);
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;
  inst.resolved = resolved;
  inst.is_bound = true;

  if (resolved) {
    BuildBoundPortBindings(item, resolved, inst);
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

using FindModuleFn = std::function<ModuleDecl*(std::string_view)>;
using ExportBuckets =
    std::unordered_map<ExportKey, std::vector<ExportSite>, ExportKeyHash>;

// §25.7: a modport reference names the interface instance and, optionally, the
// modport on that instance through which a subroutine is exported. The two
// names always travel together when resolving and recording an export.
struct ModportRef {
  std::string_view iface_inst;
  std::string_view modport;
};

// The child instance whose port bindings are scanned for modport exports: the
// resolved instance plus the module declaration that may supply out-of-block
// subroutine bodies.
struct BoundChild {
  const RtlirModuleInst& child;
  const ModuleDecl* child_decl;
};

// Shared state for one export-conflict scan: the interface-instance type map
// and module lookup used to resolve connections, the per-export-key buckets
// that accumulate matched export sites, and the diagnostic sink.
struct ExportScan {
  const std::unordered_map<std::string_view, std::string_view>&
      iface_inst_to_type;
  const FindModuleFn& find_module;
  ExportBuckets& buckets;
  DiagEngine& diag;
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
  return proto->kind != ModuleItemKind::kFunctionDecl ||
         TypesMatch(proto->data_type, body->return_type);
}

std::unordered_map<std::string_view, std::string_view>
CollectInterfaceInstances(const RtlirModule* mod,
                          const FindModuleFn& find_module) {
  std::unordered_map<std::string_view, std::string_view> iface_inst_to_type;
  for (const auto& c : mod->children) {
    if (auto* cd = find_module(c.module_name);
        cd && cd->decl_kind == ModuleDeclKind::kInterface) {
      iface_inst_to_type[c.inst_name] = c.module_name;
    }
  }
  return iface_inst_to_type;
}

// Decode a port connection expression into the interface instance name and, if
// the connection names a modport, the modport name. Returns false when the
// connection is not a plain identifier or interface.modport member access.
bool DecodeInterfaceConnection(const Expr* conn,
                               std::string_view& iface_inst_name,
                               std::string_view& modport_name) {
  if (conn->kind == ExprKind::kIdentifier) {
    iface_inst_name = conn->text;
    return true;
  }
  if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
      conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
      conn->rhs->kind == ExprKind::kIdentifier) {
    iface_inst_name = conn->lhs->text;
    modport_name = conn->rhs->text;
    return true;
  }
  return false;
}

// Record one matched export (modport port `pp` satisfied by `body`) into the
// per-export-key buckets, reporting a prototype mismatch where one applies.
void RecordExportSite(const ModportPort& pp, const ModuleItem* body,
                      const BoundChild& bound, const ModportRef& ref,
                      ExportScan& scan) {
  // §25.7: an export written as a full prototype pins the signature
  // the defining module must provide; a definition that does not
  // match it exactly is an elaboration error.
  if (pp.prototype && !ExportPrototypeMatchesBody(pp.prototype, body)) {
    scan.diag.Error(
        body->loc,
        std::format("definition of exported subroutine '{}' in module '{}' "
                    "does not match the prototype declared in the modport",
                    pp.name, bound.child.module_name));
  }
  ExportKey key{ref.iface_inst, ref.modport, pp.name};
  ExportSite site;
  site.child_inst = bound.child.inst_name;
  site.is_task = body->kind == ModuleItemKind::kTaskDecl;
  site.loc = body->loc;
  scan.buckets[key].push_back(site);
}

void CollectModportExportSites(const std::vector<ModportPort>& mp_ports,
                               const BoundChild& bound,
                               const RtlirPortBinding& binding,
                               const ModportRef& ref, ExportScan& scan) {
  for (const auto& pp : mp_ports) {
    if (!pp.is_export) continue;
    if (pp.name.empty()) continue;
    const auto* body =
        FindOutOfBlockBodyInChild(bound.child_decl, binding.port_name, pp.name);
    if (!body) continue;
    RecordExportSite(pp, body, bound, ref, scan);
  }
}

// Resolve the interface declaration a port binding connects to, decoding the
// interface instance and (optional) modport names. Returns null when the
// binding does not connect to a known interface instance.
const ModuleDecl* ResolveBoundInterface(
    const RtlirPortBinding& binding,
    const std::unordered_map<std::string_view, std::string_view>&
        iface_inst_to_type,
    const FindModuleFn& find_module, std::string_view& iface_inst_name,
    std::string_view& modport_name) {
  if (!binding.connection) return nullptr;
  if (!DecodeInterfaceConnection(binding.connection, iface_inst_name,
                                 modport_name))
    return nullptr;
  auto it = iface_inst_to_type.find(iface_inst_name);
  if (it == iface_inst_to_type.end()) return nullptr;
  return find_module(it->second);
}

// Collect export sites for one port binding, dispatching to the named modport
// or, when no modport is named, to every modport of the connected interface.
void CollectBindingExportSites(const BoundChild& bound,
                               const RtlirPortBinding& binding,
                               const ModuleDecl* iface_decl,
                               const ModportRef& ref, ExportScan& scan) {
  if (!ref.modport.empty()) {
    const auto* mp = FindModportInInterface(iface_decl, ref.modport);
    if (!mp) return;
    CollectModportExportSites(mp->ports, bound, binding, ref, scan);
    return;
  }
  for (const auto* mp : iface_decl->modports) {
    CollectModportExportSites(mp->ports, bound, binding, ref, scan);
  }
}

// Walk one child instance's port bindings, mapping every modport export it
// satisfies into the per-export-key buckets used to detect conflicts.
void CollectChildExportSites(const BoundChild& bound, ExportScan& scan) {
  for (const auto& binding : bound.child.port_bindings) {
    ModportRef ref;
    const auto* iface_decl =
        ResolveBoundInterface(binding, scan.iface_inst_to_type,
                              scan.find_module, ref.iface_inst, ref.modport);
    if (!iface_decl) continue;
    CollectBindingExportSites(bound, binding, iface_decl, ref, scan);
  }
}

void ReportDuplicateExports(
    const std::unordered_map<ExportKey, std::vector<ExportSite>, ExportKeyHash>&
        buckets,
    const std::unordered_map<std::string_view, std::string_view>&
        iface_inst_to_type,
    const FindModuleFn& find_module, DiagEngine& diag) {
  for (const auto& [key, sites] : buckets) {
    if (sites.size() < 2) continue;

    auto type_it = iface_inst_to_type.find(key.iface_inst);
    if (type_it == iface_inst_to_type.end()) continue;
    auto* iface_decl = find_module(type_it->second);
    if (!iface_decl) continue;

    const ModuleItem* prototype =
        FindInterfaceExternPrototype(iface_decl, key.name);
    bool is_task_export = sites[0].is_task;
    bool is_forkjoin_task = prototype && prototype->is_extern &&
                            prototype->is_forkjoin &&
                            prototype->kind == ModuleItemKind::kTaskDecl;

    if (is_task_export && is_forkjoin_task) continue;

    if (!is_task_export) {
      diag.Error(sites[0].loc,
                 std::format("function '{}' exported by more than one module "
                             "connected to interface instance '{}' (§25.7.4: "
                             "multiple export of functions is not allowed)",
                             key.name, key.iface_inst));
    } else {
      diag.Error(
          sites[0].loc,
          std::format("task '{}' exported by more than one module connected "
                      "to interface instance '{}' (§25.7.4: declare the task "
                      "as `extern forkjoin` in the interface to allow "
                      "multiple exports)",
                      key.name, key.iface_inst));
    }
  }
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

  FindModuleFn find_module = [this](std::string_view name) {
    return FindModule(name);
  };

  auto iface_inst_to_type = CollectInterfaceInstances(mod, find_module);

  ExportBuckets buckets;
  ExportScan scan{iface_inst_to_type, find_module, buckets, diag_};

  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto* child_decl = FindModule(child.module_name);
    if (!child_decl) continue;
    if (child_decl->decl_kind == ModuleDeclKind::kInterface) continue;

    CollectChildExportSites(BoundChild{child, child_decl}, scan);
  }

  ReportDuplicateExports(buckets, iface_inst_to_type, find_module, diag_);

  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    WalkForExportConflicts(child.resolved, visited);
  }
}

}  // namespace delta
