#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_bind_params.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_modport_imports.h"
#include "elaborator/elaborator_module_inst_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsBindTargetScope(std::string_view target,
                              const CompilationUnit* unit) {
  if (target.find('.') != std::string_view::npos) return false;
  for (auto* m : unit->modules)
    if (m->name == target) return true;
  for (auto* i : unit->interfaces)
    if (i->name == target) return true;
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

struct BindDirectiveSite {
  BindDirective* bd;
  std::string_view owner;
};

static std::vector<BindDirectiveSite> CollectBindDirectives(
    const CompilationUnit* unit) {
  std::vector<BindDirectiveSite> binds;
  binds.reserve(unit->bind_directives.size());
  for (auto* bd : unit->bind_directives) binds.push_back({bd, {}});
  for (const auto* decls :
       {&unit->modules, &unit->interfaces, &unit->programs}) {
    for (auto* decl : *decls) {
      for (auto* bd : decl->bind_directives) binds.push_back({bd, decl->name});
    }
  }
  return binds;
}

static std::string_view LastPathSegment(std::string_view path) {
  size_t dot = path.rfind('.');
  return dot == std::string_view::npos ? path : path.substr(dot + 1);
}

static bool BindTargetsInstance(const BindDirective* bd,
                                std::string_view module, std::string_view inst,
                                const CompilationUnit* unit) {
  if (!IsBindTargetScope(bd->target.path, unit))
    return LastPathSegment(bd->target.path) == inst;
  if (bd->target.path != module) return false;
  if (bd->target_instances.empty()) return true;
  return std::any_of(bd->target_instances.begin(), bd->target_instances.end(),
                     [&](const BindTargetInstance& target) {
                       return LastPathSegment(target.path) == inst;
                     });
}

bool BindIntroducesName(const CompilationUnit* unit, std::string_view module,
                        std::string_view inst, std::string_view name) {
  for (const auto& site : CollectBindDirectives(unit)) {
    const ModuleItem* item = site.bd->instantiation;
    if (item != nullptr && item->inst_name == name &&
        BindTargetsInstance(site.bd, module, inst, unit))
      return true;
  }
  return false;
}

struct BindWalkState {
  const std::vector<BindDirectiveSite>& binds;
  std::unordered_set<RtlirModule*> visited;
  std::unordered_set<const BindDirective*> applied;
  std::unordered_set<const BindTargetInstance*> matched;
  std::unordered_map<std::string, std::string_view> path_modules;
  std::unordered_map<const BindTargetInstance*, std::string> paths;
};

static std::string SelectedTargetPath(const BindTargetInstance& target,
                                      const ScopeMap& scope, SourceLoc loc,
                                      DiagEngine& diag) {
  std::string path;
  for (const BindTargetSegment& segment : target.segments) {
    if (!path.empty()) path.push_back('.');
    path.append(segment.name);
    for (const Expr* select : segment.selects) {
      std::optional<int64_t> index;
      if (IsConstantExpr(select, scope)) index = ConstEvalInt(select, scope);
      if (!index) {
        diag.Error(loc,
                   "a bind target selects with an expression that is not "
                   "constant",
                   Subclause("A.1.4"));
        path.append("[]");
        continue;
      }
      path += std::format("[{}]", *index);
    }
  }
  return path;
}

struct Elaborator::BindWalkCtx : BindWalkState {};

static void ReportUnmatchedBindTargets(const BindWalkState& ctx,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  for (const auto& site : ctx.binds) {
    const BindDirective* bd = site.bd;
    for (const auto& inst : bd->target_instances) {
      if (ctx.matched.count(&inst)) continue;
      diag.Error(bd->loc,
                 std::format("bind target instance '{}' is no instance of '{}'",
                             inst.path, bd->target.path),
                 Subclause("23.11"));
    }
    if (ctx.applied.count(bd)) continue;
    if (IsBindTargetScope(bd->target.path, unit)) continue;
    diag.Error(bd->loc,
               std::format("bind target '{}' is neither a module or interface "
                           "scope nor an instance",
                           bd->target.path),
               Subclause("23.11"));
  }
}

static const RtlirModule* AnInstanceOf(const std::vector<RtlirModule*>& tops,
                                       std::string_view name) {
  std::vector<const RtlirModule*> pending(tops.begin(), tops.end());
  std::unordered_set<const RtlirModule*> seen;
  while (!pending.empty()) {
    const RtlirModule* mod = pending.back();
    pending.pop_back();
    if (mod == nullptr || !seen.insert(mod).second) continue;
    if (mod->name == name) return mod;
    for (const auto& child : mod->children) pending.push_back(child.resolved);
  }
  return nullptr;
}

void Elaborator::ApplyBindDirectives(const std::vector<RtlirModule*>& tops) {
  std::vector<BindDirectiveSite> binds = CollectBindDirectives(unit_);
  std::erase_if(binds, [this](const BindDirectiveSite& site) {
    return site.bd->in_generate_block && !generate_binds_.contains(site.bd);
  });
  generate_binds_.clear();
  if (binds.empty()) return;
  BindWalkCtx ctx{{binds, {}, {}, {}, {}, {}}};
  for (const auto& site : binds) {
    const RtlirModule* owner =
        site.owner.empty() ? nullptr : AnInstanceOf(tops, site.owner);
    const ScopeMap kScope = owner ? BuildParamScope(owner) : ScopeMap{};
    const BindDirective* bd = site.bd;
    ctx.paths[&bd->target] =
        SelectedTargetPath(bd->target, kScope, bd->loc, diag_);
    for (const auto& inst : bd->target_instances) {
      ctx.paths[&inst] = SelectedTargetPath(inst, kScope, bd->loc, diag_);
    }
  }
  for (auto* top : tops) {
    if (top) WalkForBind(top, std::string(top->name), false, ctx);
  }
  ReportUnmatchedBindTargets(ctx, unit_, diag_);
  ReportBindParamsInConstants(
      tops, [this](std::string_view name) { return FindModule(name); }, diag_);
}

static bool TargetInstanceNames(const BindTargetInstance& target,
                                std::string_view owner,
                                const std::string& hier_path,
                                const BindWalkState& ctx) {
  std::string_view path = hier_path;
  std::string_view written = ctx.paths.at(&target);
  if (path == written) return true;
  if (target.from_root || owner.empty()) return false;
  if (path.size() <= written.size() + 1) return false;
  size_t cut = path.size() - written.size() - 1;
  if (path[cut] != '.' || path.substr(cut + 1) != written) return false;
  auto it = ctx.path_modules.find(std::string(path.substr(0, cut)));
  return it != ctx.path_modules.end() && it->second == owner;
}

static bool BindAppliesToModule(const BindDirectiveSite& site,
                                const RtlirModule* mod,
                                const std::string& hier_path,
                                const CompilationUnit* unit,
                                BindWalkState& ctx) {
  const BindDirective* bd = site.bd;
  if (!IsBindTargetScope(bd->target.path, unit)) {
    return TargetInstanceNames(bd->target, site.owner, hier_path, ctx);
  }
  if (mod->name != bd->target.path) return false;
  if (bd->target_instances.empty()) return true;
  bool named = false;
  for (const auto& inst : bd->target_instances) {
    if (!TargetInstanceNames(inst, site.owner, hier_path, ctx)) continue;
    ctx.matched.insert(&inst);
    named = true;
  }
  return named;
}

static std::string BindChildPath(const std::string& hier_path,
                                 const RtlirModuleInst& child) {
  std::string path =
      HierInstancePath(hier_path, child.gen_block_path, child.simple_inst_name);
  std::string_view flat = child.inst_name;
  if (flat.ends_with(']')) path.append(flat.substr(flat.rfind('[')));
  return path;
}

static bool BindNamesArrayElement(const RtlirModuleInst& elem,
                                  const std::string& path,
                                  const CompilationUnit* unit,
                                  BindWalkState& ctx) {
  if (elem.array.name.empty()) return false;
  return std::ranges::any_of(ctx.binds, [&](const BindDirectiveSite& site) {
    const BindDirective* bd = site.bd;
    if (IsBindTargetScope(bd->target.path, unit) &&
        bd->target_instances.empty()) {
      return false;
    }
    return BindAppliesToModule(site, elem.resolved, path, unit, ctx);
  });
}

void Elaborator::WalkForBind(RtlirModule* mod, const std::string& hier_path,
                             bool under_bind, BindWalkCtx& ctx) {
  if (!mod) return;
  if (!ctx.visited.insert(mod).second) return;
  ctx.path_modules.emplace(hier_path, mod->name);

  for (const auto& site : ctx.binds) {
    if (!BindAppliesToModule(site, mod, hier_path, unit_, ctx)) continue;
    ctx.applied.insert(site.bd);
    if (under_bind) {
      diag_.Error(site.bd->loc,
                  "bind target shall not be a scope created by a bind",
                  Subclause("23.11"));
      continue;
    }
    ApplyBindInstance(site.bd, mod);
  }

  for (auto& c : mod->children) {
    if (c.resolved &&
        BindNamesArrayElement(c, BindChildPath(hier_path, c), unit_, ctx)) {
      IsolateArrayElement(*mod, c, arena_);
    }
  }
  for (auto& c : mod->children) {
    if (!c.resolved) continue;
    bool child_under_bind = under_bind || c.is_bound;
    WalkForBind(c.resolved, BindChildPath(hier_path, c), child_under_bind, ctx);
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

static bool TargetReferencesName(const RtlirModule* target,
                                 std::string_view name) {
  if (std::ranges::any_of(target->assigns, [name](const RtlirContAssign& ca) {
        return ExprContainsIdent(ca.lhs, name) ||
               ExprContainsIdent(ca.rhs, name);
      })) {
    return true;
  }
  std::vector<const Expr*> reads;
  for (const auto& proc : target->processes) {
    CollectProcRhsIdents(proc.body, {}, reads);
  }
  return std::ranges::any_of(
      reads, [name](const Expr* read) { return read->text == name; });
}

static bool TargetSeesSignal(const RtlirModule* target,
                             const CompilationUnit* unit,
                             std::string_view name) {
  return TargetHasSignal(target, name) ||
         ImportBringsInSignal(target, unit, name, false) ||
         (ImportBringsInSignal(target, unit, name, true) &&
          TargetReferencesName(target, name));
}

struct BindConnScopes {
  const RtlirModule* target;
  const ModuleDecl* bound;
  const CompilationUnit* unit;
};

static bool ValidateBindPortConnections(const BindDirective* bd,
                                        const ModuleItem* item,
                                        const BindConnScopes& scopes,
                                        DiagEngine& diag) {
  const RtlirModule* target = scopes.target;
  const ModuleDecl* bound = scopes.bound;
  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto [pname, conn_expr] = item->inst_ports[i];
    if (!conn_expr || conn_expr->kind != ExprKind::kIdentifier) continue;
    if (pname.empty() && i < bound->ports.size()) pname = bound->ports[i].name;
    auto name = conn_expr->text;
    if (!TargetSeesSignal(target, scopes.unit, name)) {
      diag.Error(bd->loc,
                 std::format("bind port connection '{}' references "
                             "undeclared signal '{}' in target scope '{}'",
                             pname, name, target->name),
                 Subclause("23.11"));
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
  inst.ports_by_name = !kIsOrdered;
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

static void BuildBoundWildcardBindings(const ModuleItem* item,
                                       const RtlirModule* resolved,
                                       const RtlirModule* target, Arena& arena,
                                       RtlirModuleInst& inst) {
  for (const auto& port : resolved->ports) {
    bool explicit_conn =
        std::any_of(item->inst_ports.begin(), item->inst_ports.end(),
                    [&](const auto& conn) { return conn.first == port.name; });
    if (explicit_conn) continue;
    RtlirPortBinding binding;
    binding.port_name = port.name;
    binding.direction = port.direction;
    binding.width = port.width;
    if (TargetHasSignal(target, port.name)) {
      auto* expr = arena.Create<Expr>();
      expr->kind = ExprKind::kIdentifier;
      expr->text = port.name;
      binding.connection = expr;
    } else {
      binding.connection = port.default_value;
      binding.unconnected = true;
    }
    if (binding.connection) inst.port_bindings.push_back(binding);
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
                              item->inst_module, target->name),
                  Subclause("23.11"));
      return;
    }
  }

  auto declared = CollectDeclaredNames(target);
  if (!item->inst_name.empty() && declared.count(item->inst_name)) {
    diag_.Error(bd->loc,
                std::format("bind instance name '{}' clashes with "
                            "existing name in target scope '{}'",
                            item->inst_name, target->name),
                Subclause("23.11"));
    return;
  }

  auto* child_decl = FindModule(item->inst_module);
  if (!child_decl) {
    diag_.Error(
        bd->loc,
        std::format("bind refers to unknown module '{}'", item->inst_module),
        Subclause("23.3.2"));
    return;
  }

  if (!ValidateBindPortConnections(bd, item, {target, child_decl, unit_},
                                   diag_)) {
    return;
  }

  ParamList child_params;
  ScopeMap target_scope = BuildParamScope(target, {});
  ResolveInstParams(item, child_decl, target_scope, child_params, diag_);
  auto* resolved = ElaborateModule(child_decl, child_params);
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;
  inst.simple_inst_name = item->inst_name;
  inst.resolved = resolved;
  inst.is_bound = true;

  if (resolved) {
    BuildBoundPortBindings(item, resolved, inst);
    if (item->inst_wildcard) {
      BuildBoundWildcardBindings(item, resolved, target, arena_, inst);
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

using FindModuleFn = std::function<ModuleDecl*(std::string_view)>;
using ExportBuckets =
    std::unordered_map<ExportKey, std::vector<ExportSite>, ExportKeyHash>;

struct ModportRef {
  std::string_view iface_inst;
  std::string_view modport;
};

struct BoundChild {
  const RtlirModuleInst& child;
  const ModuleDecl* child_decl;
};

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

void RecordExportSite(const ModportPort& pp, const ModuleItem* body,
                      const BoundChild& bound, const ModportRef& ref,
                      ExportScan& scan) {
  if (pp.prototype && !PrototypeMatchesSubroutine(pp.prototype, body)) {
    scan.diag.Error(
        body->loc,
        std::format("definition of exported subroutine '{}' in module '{}' "
                    "does not match the prototype declared in the modport",
                    pp.name, bound.child.module_name),
        Subclause("25.7"));
  }
  ExportKey key{ref.iface_inst, ref.modport, pp.name};
  ExportSite site;
  site.child_inst = bound.child.inst_name;
  site.is_task = body->kind == ModuleItemKind::kTaskDecl;
  site.loc = body->loc;
  scan.buckets[key].push_back(site);
}

void CollectModportExportSites(const ModportDecl* mp, const BoundChild& bound,
                               const RtlirPortBinding& binding,
                               const ModportRef& ref, ExportScan& scan) {
  for (const auto& pp : mp->ports) {
    if (!pp.is_export) continue;
    if (pp.name.empty()) continue;
    const auto* body =
        FindOutOfBlockBodyInChild(bound.child_decl, binding.port_name, pp.name);
    if (!body) {
      if (!ref.modport.empty()) {
        scan.diag.Error(
            pp.prototype ? pp.prototype->loc : mp->loc,
            std::format(
                "module '{}' is connected to modport '{}' of interface "
                "instance '{}', which exports subroutine '{}', but the module "
                "does not define it",
                bound.child.module_name, ref.modport, ref.iface_inst, pp.name),
            Subclause("25.7"));
      }
      continue;
    }
    RecordExportSite(pp, body, bound, ref, scan);
  }
}

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

void CollectBindingExportSites(const BoundChild& bound,
                               const RtlirPortBinding& binding,
                               const ModuleDecl* iface_decl,
                               const ModportRef& ref, ExportScan& scan) {
  if (!ref.modport.empty()) {
    const auto* mp = FindModportInInterface(iface_decl, ref.modport);
    if (!mp) return;
    CollectModportExportSites(mp, bound, binding, ref, scan);
    return;
  }
  for (const auto* mp : iface_decl->modports) {
    CollectModportExportSites(mp, bound, binding, ref, scan);
  }
}

bool InterfaceAnnouncesSubroutine(const ModuleDecl* iface,
                                  std::string_view name) {
  if (FindInterfaceExternPrototype(iface, name)) return true;
  for (const auto* mp : iface->modports) {
    for (const auto& pp : mp->ports) {
      if (pp.is_export && pp.name == name) return true;
    }
  }
  return false;
}

void CheckHierarchicalBodiesAnnounced(const BoundChild& bound,
                                      const RtlirPortBinding& binding,
                                      const ModuleDecl* iface_decl,
                                      ExportScan& scan) {
  for (const auto* item : bound.child_decl->items) {
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl)
      continue;
    if (item->method_class != binding.port_name) continue;
    if (InterfaceAnnouncesSubroutine(iface_decl, item->name)) continue;
    scan.diag.Error(
        item->loc,
        std::format(
            "subroutine '{}' defined in module '{}' for interface port '{}' by "
            "a hierarchical name is neither declared 'extern' in interface "
            "'{}' "
            "nor exported by any of its modports",
            item->name, bound.child.module_name, binding.port_name,
            iface_decl->name),
        Subclause("25.7"));
  }
}

void CollectChildExportSites(const BoundChild& bound, ExportScan& scan) {
  for (const auto& binding : bound.child.port_bindings) {
    ModportRef ref;
    const auto* iface_decl =
        ResolveBoundInterface(binding, scan.iface_inst_to_type,
                              scan.find_module, ref.iface_inst, ref.modport);
    if (!iface_decl) continue;
    CheckHierarchicalBodiesAnnounced(bound, binding, iface_decl, scan);
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
                             "connected to interface instance '{}' (multiple "
                             "export of functions is not allowed)",
                             key.name, key.iface_inst),
                 Subclause("25.7.4"));
    } else {
      diag.Error(
          sites[0].loc,
          std::format("task '{}' exported by more than one module connected "
                      "to interface instance '{}' (declare the task as "
                      "`extern forkjoin` in the interface to allow "
                      "multiple exports)",
                      key.name, key.iface_inst),
          Subclause("25.7.4"));
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
