#include "simulator/vpi_design_attach.h"

#include <cstddef>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_io_decl.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"
#include "simulator/clocking.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_interconnects.h"
#include "simulator/vpi_design_attach_typespecs.h"
#include "simulator/vpi_design_attach_vars.h"
#include "simulator/vpi_design_prefixed_refs.h"
#include "simulator/vpi_design_viewports.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_source_delay.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

void RecordSourceLocation(VpiHandle obj, SourceLoc loc,
                          const SourceManager* sources) {
  if (obj == nullptr || sources == nullptr || !loc.IsValid()) return;
  const SourceLoc kWritten = sources->ResolveToOrigin(loc);
  obj->line_no = static_cast<int>(kWritten.line);
  obj->file = std::string(sources->FilePath(kWritten.file_id));
}

void RecordProtection(VpiHandle obj, SourceLoc loc,
                      const SourceManager* sources) {
  if (obj == nullptr || sources == nullptr) return;
  if (sources->IsProtected(loc)) obj->is_protected = true;
}

const SourceManager* SourcesOf(SimContext* sim_ctx) {
  return sim_ctx == nullptr ? nullptr : &sim_ctx->GetDiag().Sources();
}

}  // namespace

VpiHandle VpiContext::DesignScopeChild(VpiHandle parent, std::string_view part,
                                       std::string_view full_path) {
  if (parent == nullptr) {
    auto it = object_map_.find(part);
    if (it != object_map_.end()) return it->second;
  } else {
    VpiHandle existing = ChildNamed(parent, part);
    if (existing != nullptr) return existing;
  }

  name_pool_.emplace_back(part);
  auto* obj = AllocObject();
  obj->type = kVpiModule;
  obj->name = name_pool_.back();
  obj->full_name = std::string(full_path);
  obj->parent = parent;
  if (parent == nullptr) {
    object_map_[obj->name] = obj;
  } else {
    obj->index = static_cast<int>(parent->children.size());
    parent->children.push_back(obj);
  }
  return obj;
}

VpiHandle VpiContext::DesignObjectForFlatName(std::string_view flat_name) {
  std::vector<std::string_view> parts =
      VpiNamePathComponents(flat_name, dotted_escaped_names_);
  if (parts.empty()) return nullptr;

  VpiHandle current = nullptr;
  std::size_t consumed = 0;
  for (std::string_view part : parts) {
    consumed += part.size();
    current = DesignScopeChild(current, part, flat_name.substr(0, consumed));
    consumed += 1;
  }
  return current;
}

namespace {

int VpiPortDirectionOf(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      return kVpiInput;
    case Direction::kOutput:
      return kVpiOutput;
    case Direction::kInout:
      return kVpiInout;
    case Direction::kRef:
      return vpiRef;
    default:
      return 0;
  }
}

void FillPortObject(VpiObject* obj, const RtlirPort& port, int index,
                    VpiHandle module, std::deque<std::string>& names) {
  obj->type = kVpiPort;
  names.emplace_back(port.name);
  obj->name = names.back();
  obj->index = index;
  obj->size = static_cast<int>(port.width);
  obj->direction = VpiPortDirectionOf(port.direction);
  obj->port_type = VpiPortTypeFromFormal(
      port.is_interface_port, !port.declared_type->modport_name.empty());
  obj->explicit_name = port.is_explicit_named;
  obj->parent = module;
  module->children.push_back(obj);
}

void MakeModuleIoDecl(const RtlirIoDecl& decl, VpiHandle module,
                      VpiObject* item, const std::function<VpiObject*()>& alloc,
                      std::deque<std::string>& names) {
  VpiObject* io_decl = alloc();
  io_decl->type = vpiIODecl;
  names.emplace_back(decl.name);
  io_decl->name = names.back();
  io_decl->full_name = VpiScopedFullName(module, decl.name);
  io_decl->parent = module;
  const bool kByRef = decl.direction == Direction::kRef;
  io_decl->direction =
      VpiIoDeclDirection(VpiPortDirectionOf(decl.direction), kByRef,
                         decl.is_interface_port, false);
  io_decl->io_expr = item;
  if (kByRef || decl.is_interface_port) {
    VpiObject* ref_obj = alloc();
    ref_obj->type = vpiRefObj;
    ref_obj->parent = io_decl;
    ref_obj->name = io_decl->name;
    ref_obj->full_name = io_decl->full_name;
    ref_obj->actual = item;
    io_decl->io_expr = ref_obj;
  }
  module->children.push_back(io_decl);
}

VpiObject* PortIoDeclItem(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const std::string& prefix, const RtlirPort& port) {
  if (port.is_interface_port) return nullptr;
  return FindObjectForFlatName(objects, VpiFlatName(prefix, port.name));
}

VpiObject* IoDeclItem(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const std::string& prefix, const RtlirIoDecl& decl) {
  if (decl.object_name.empty()) return nullptr;
  return FindObjectForFlatName(objects, VpiFlatName(prefix, decl.object_name));
}

void FillInterconnectNetObject(VpiObject* obj, const RtlirPort& port,
                               VpiObject* port_obj) {
  if (obj == nullptr) return;
  obj->type = vpiInterconnectNet;
  obj->size = static_cast<int>(port.width);
  port_obj->low_conn = obj;
}

void RecordVariableObjectKinds(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    SimContext& ctx) {
  if (design == nullptr) return;
  VpiRecordScopeVariableKinds(*design, objects, ctx);

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
          VpiHandle obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj == nullptr) continue;
          obj->type = VpiVariableObjectKind(var, *design, *mod);
          obj->decl_facts.constant_variable =
              var.written_type != nullptr && var.written_type->is_const;
          obj->decl_facts.vif_interface =
              VpiVirtualInterfaceOf(*design, var.written_type, mod);
          obj->is_modport = var.written_type != nullptr &&
                            !var.written_type->modport_name.empty();
        }
      });
}

void RecordDeclarationSourceLocations(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager* sources) {
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : mod->nets) {
          RecordSourceLocation(
              FindObjectForFlatName(objects, VpiFlatName(prefix, net.name)),
              net.loc.IsValid() ? net.loc : net.implicit_ref_loc, sources);
        }
        for (const RtlirVariable& var : mod->variables) {
          RecordSourceLocation(
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name)),
              var.loc, sources);
        }
      });
}

void RecordProtectedDeclarations(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager* sources) {
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        std::string_view instance = prefix.empty() ? mod->name : prefix;
        RecordProtection(FindObjectForFlatName(objects, instance), mod->loc,
                         sources);
        for (const RtlirNet& net : mod->nets) {
          RecordProtection(
              FindObjectForFlatName(objects, VpiFlatName(prefix, net.name)),
              net.loc, sources);
        }
        for (const RtlirVariable& var : mod->variables) {
          RecordProtection(
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name)),
              var.loc, sources);
        }
      });
}

}  // namespace

void VpiContext::AttachDesignPorts(const RtlirDesign* design) {
  if (design == nullptr) return;

  const std::function<VpiObject*()> kAlloc = [this] { return AllocObject(); };
  const VpiNameKeeper kKeep = VpiPoolKeeper(name_pool_);
  WalkInstanceObjects(
      design, object_map_,
      [this, &kAlloc](const RtlirModule* mod, const std::string& prefix,
                      VpiHandle module) {
        if (module == nullptr) return;

        module->children.reserve(module->children.size() + mod->ports.size());
        int index = 0;
        const SourceManager* sources = SourcesOf(sim_ctx_);
        for (const auto& port : mod->ports) {
          VpiObject* net =
              port.is_interconnect
                  ? DesignObjectForFlatName(VpiFlatName(prefix, port.name))
                  : nullptr;
          auto* obj = AllocObject();
          FillPortObject(obj, port, index++, module, name_pool_);
          RecordSourceLocation(obj, port.loc, sources);
          RecordProtection(obj, port.loc, sources);
          FillInterconnectNetObject(net, port, obj);
          if (port.port_expr == nullptr) {
            MakeModuleIoDecl(
                {port.name, port.direction, port.name, port.is_interface_port},
                module, PortIoDeclItem(object_map_, prefix, port), kAlloc,
                name_pool_);
          }
        }
        for (const RtlirIoDecl& decl : mod->port_expr_decls) {
          MakeModuleIoDecl(decl, module, IoDeclItem(object_map_, prefix, decl),
                           kAlloc, name_pool_);
        }
      });
  if (sim_ctx_ == nullptr) return;
  std::vector<VpiDeferredCall> deferred;
  const VpiAttachBuild kBuild{kAlloc, kKeep, sim_ctx_->GetArena(), &deferred,
                              call_objects_.unit_typespecs};
  AttachPortConnections(design, object_map_, *sim_ctx_, kBuild);
  VpiShapeDeferredCalls(design, object_map_, deferred, CallBuild(), kBuild);
  AttachPortAttributes(design, object_map_, *sim_ctx_, kBuild);
  AttachPortTypespecs(design, object_map_, call_objects_, *sim_ctx_, kBuild);
  AttachInterconnectPorts(design, object_map_, *sim_ctx_, kBuild);
  AttachInterconnectTypespecs(design, object_map_, kBuild);
}

namespace {

struct InterModPortRef {
  std::string inst_path;
  std::string_view port_name;
  std::string_view signal;
  Direction direction;
};

struct InterModConnection {
  std::string from_inst;
  std::string_view from_port;
  std::string to_inst;
  std::string_view to_port;
};

std::string_view ConnectedSignalName(const Expr* conn) {
  if (conn == nullptr || conn->kind != ExprKind::kIdentifier) return {};
  return conn->text;
}

bool InterModPathRuns(const InterModPortRef& from, const InterModPortRef& to) {
  if (&from == &to) return false;
  if (from.signal != to.signal) return false;
  const bool kDrives = from.direction == Direction::kOutput ||
                       from.direction == Direction::kInout;
  const bool kReceives =
      to.direction == Direction::kInput || to.direction == Direction::kInout;
  return kDrives && kReceives;
}

void CollectScopePortRefs(const RtlirModule* mod, const std::string& prefix,
                          std::vector<InterModPortRef>& refs) {
  for (const auto& child : mod->children) {
    std::string inst_path = prefix;
    if (!inst_path.empty()) inst_path += '.';
    inst_path += std::string(child.inst_name);
    refs.reserve(refs.size() + child.port_bindings.size());
    for (const auto& binding : child.port_bindings) {
      std::string_view signal = ConnectedSignalName(binding.connection);
      if (signal.empty()) continue;
      refs.push_back({inst_path, binding.port_name, signal, binding.direction});
    }
  }
}

void PairOnePortRef(const InterModPortRef& from,
                    const std::vector<InterModPortRef>& refs,
                    std::vector<InterModConnection>& out) {
  out.reserve(out.size() + refs.size());
  for (const auto& to : refs) {
    if (!InterModPathRuns(from, to)) continue;
    out.push_back({from.inst_path, from.port_name, to.inst_path, to.port_name});
  }
}

void PairScopePortRefs(const std::vector<InterModPortRef>& refs,
                       std::vector<InterModConnection>& out) {
  for (const auto& from : refs) PairOnePortRef(from, refs, out);
}

void CollectInterModConnections(const RtlirDesign* design,
                                std::vector<InterModConnection>& out) {
  WalkInstancePaths(design,
                    [&out](const RtlirModule* mod, const std::string& prefix) {
                      std::vector<InterModPortRef> refs;
                      CollectScopePortRefs(mod, prefix, refs);
                      PairScopePortRefs(refs, out);
                    });
}

VpiObject* DesignPortObject(VpiHandle module, std::string_view port_name) {
  if (module == nullptr) return nullptr;
  for (auto* child : module->children) {
    if (child->type == kVpiPort && child->name == port_name) return child;
  }
  return nullptr;
}

}  // namespace

void VpiContext::AttachDesignInterModPaths(const RtlirDesign* design) {
  if (design == nullptr) return;

  std::vector<InterModConnection> conns;
  CollectInterModConnections(design, conns);
  for (const InterModConnection& conn : conns) {
    VpiObject* from = DesignPortObject(DesignObjectForFlatName(conn.from_inst),
                                       conn.from_port);
    VpiObject* to =
        DesignPortObject(DesignObjectForFlatName(conn.to_inst), conn.to_port);
    if (from == nullptr || to == nullptr) continue;

    auto* path = AllocObject();
    path->type = vpiInterModPath;
    path->children.push_back(from);
    path->children.push_back(to);
    from->children.push_back(path);
    to->children.push_back(path);
  }
}

void VpiContext::AttachSourceDelayExpressions(SimContext& sim_ctx,
                                              const RtlirDesign* design) {
  if (design == nullptr) return;

  WalkInstancePaths(design, [&](const RtlirModule* mod,
                                const std::string& prefix) {
    for (const RtlirNet& net : mod->nets) {
      VpiHandle obj =
          FindObjectForFlatName(object_map_, VpiFlatName(prefix, net.name));
      if (obj == nullptr) continue;
      obj->delay_expr = VpiSourceDelayExpression(
          {net.delay_rise, net.delay_fall, net.delay_turnoff},
          VpiFlatName(prefix, ""), sim_ctx, [this] { return AllocObject(); });
    }
  });
}

void VpiContext::AttachUdpDefns(const RtlirDesign* design) {
  for (const UdpDecl* decl : VpiDesignUdpDecls(design)) {
    auto* defn = AllocObject();
    VpiFillUdpDefnObject(defn, *decl, name_pool_);
    RecordProtection(defn, decl->range.start, SourcesOf(sim_ctx_));
    run_objects_.try_emplace(decl, defn);
    const auto kIoDecl = [&](std::string_view name, int direction) {
      auto* io_decl = AllocObject();
      io_decl->type = vpiIODecl;
      name_pool_.emplace_back(name);
      io_decl->name = name_pool_.back();
      io_decl->full_name = std::string(decl->name) + "." + std::string(name);
      io_decl->parent = defn;
      io_decl->direction = direction;
      io_decl->size = 1;
      defn->children.push_back(io_decl);
    };
    kIoDecl(decl->output_name, vpiOutput);
    for (std::string_view input : decl->input_names) kIoDecl(input, vpiInput);
    for (const UdpTableRow& row : decl->table) {
      VpiFillUdpTableEntryObject(AllocObject(), row, defn,
                                 sim_ctx_->GetArena());
    }
    if (decl->has_initial) {
      auto* initial = AllocObject();
      initial->type = vpiInitial;
      initial->parent = defn;
      initial->body = VpiUdpInitialStatement(
          *decl, initial, [this] { return AllocObject(); }, name_pool_,
          sim_ctx_->GetArena());
      defn->children.push_back(initial);
    }
  }
}

namespace {

bool HasNoObjectAtItsKey(SimContext& sim_ctx, std::string_view name,
                         const Variable* var) {
  if (sim_ctx.IsImportedName(name) || sim_ctx.IsBlockVariable(name)) {
    return true;
  }
  const ClockingManager* clocking = sim_ctx.GetClockingManager();
  return clocking != nullptr && clocking->IsBlockEventVar(var);
}

}  // namespace

void VpiContext::Attach(SimContext& sim_ctx, const RtlirDesign* design) {
  sim_ctx_ = &sim_ctx;
  dotted_escaped_names_ = VpiDottedEscapedNames(design);

  for (auto& [name, var] : sim_ctx.GetVariables()) {
    if (HasNoObjectAtItsKey(sim_ctx, name, var)) continue;
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || var == nullptr) continue;
    obj->type = kVpiReg;
    obj->actual_origin = kVpiActualStaticElab;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
  }
  AttachInstanceObjects(design);
  AttachModuleDefNames(sim_ctx);
  for (auto& [name, net] : sim_ctx.GetNets()) {
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || net == nullptr) continue;
    obj->type = kVpiNet;
    obj->actual_origin = kVpiActualStaticElab;
    obj->net = net;
    if (net->resolved != nullptr) {
      obj->var = net->resolved;
      obj->size = static_cast<int>(net->resolved->value.width);
    }
  }
  AttachSourceDelayExpressions(sim_ctx, design);
  RecordVariableObjectKinds(design, object_map_, sim_ctx);
  RecordDeclarationSourceLocations(design, object_map_, SourcesOf(sim_ctx_));
  AttachPackages(design);
  AttachTopModules(design);
  AttachUdpDefns(design);
  AttachInstanceContents(design);
  AttachModulePathDelays(sim_ctx);
  AttachTimingChecks(sim_ctx);
  RecordProtectedDeclarations(design, object_map_, SourcesOf(sim_ctx_));
  RecordViewportGrants(design, object_map_, sim_ctx.GetDiag().Sources());
  AttachNettypeDeclarations(design);
}

namespace {

void PrefixFullNamesWithTop(VpiObject* obj, std::string_view top) {
  if (obj == nullptr) return;
  if (!obj->full_name.empty()) {
    obj->full_name = std::string(top) + "." + obj->full_name;
  }
  for (auto* child : obj->children) PrefixFullNamesWithTop(child, top);
}

struct NettypeScope {
  const VpiObject& scope;
  const std::vector<RtlirImport>& imports;
};

VpiObject* NettypeTypespec(const DataType& type, const NettypeScope& at,
                           VpiObject* decl, SimContext& ctx,
                           const VpiAttachBuild& build) {
  if (type.kind != DataTypeKind::kNamed) {
    return VpiKeywordTypespec(type, decl, ctx, build);
  }
  for (VpiObject* child : at.scope.children) {
    if (type.scope_name.empty() && VpiIsTypespecType(child->type) &&
        child->name == type.type_name) {
      return child;
    }
  }
  return VpiPackageOrUnitTypespec(type.scope_name, type.type_name, at.imports,
                                  build.unit_typespecs);
}

}  // namespace

void VpiContext::MakeNettypeDecls(VpiHandle scope,
                                  const std::vector<ModuleItem*>& items,
                                  const std::vector<RtlirImport>& imports) {
  const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                              VpiPoolKeeper(name_pool_), sim_ctx_->GetArena(),
                              nullptr, call_objects_.unit_typespecs};
  for (const ModuleItem* entry : items) {
    if (entry->kind != ModuleItemKind::kNettypeDecl) continue;
    const ModuleItem& item = *entry;
    name_pool_.emplace_back(item.name);
    auto* decl = AllocObject();
    decl->type = vpiNettypeDecl;
    decl->name = name_pool_.back();
    decl->full_name = VpiScopedFullName(scope, item.name);
    decl->parent = scope;
    decl->in_compilation_unit = scope->in_compilation_unit;
    for (auto* earlier : scope->children) {
      if (earlier->type == vpiNettypeDecl &&
          earlier->name == item.typedef_type.type_name) {
        decl->aliased = earlier;
        decl->nettype_with = earlier->nettype_with;
      }
    }
    if (decl->aliased != nullptr) {
      decl->children = decl->aliased->children;
    } else if (VpiObject* typespec =
                   NettypeTypespec(item.typedef_type, {*scope, imports}, decl,
                                   *sim_ctx_, kBuild)) {
      decl->children.push_back(typespec);
    }
    scope->children.push_back(decl);

    if (!item.nettype_resolve_func.empty()) {
      name_pool_.emplace_back(item.nettype_resolve_func);
      auto* func = AllocObject();
      func->type = vpiFunction;
      func->name = name_pool_.back();
      func->parent = scope;
      decl->nettype_with = func;
    }
  }
}

void VpiContext::AttachNettypeDeclarations(const RtlirDesign* design) {
  WalkInstanceObjects(
      design, object_map_,
      [&](const RtlirModule* mod, const std::string&, VpiObject* scope) {
        MakeNettypeDecls(scope, VpiDeclOf(*mod).items, mod->imports);
      });
  if (design == nullptr) return;
  static const std::vector<RtlirImport> kNoImports;
  for (const PackageDecl* pkg : design->packages) {
    MakeNettypeDecls(DesignObjectForFlatName(pkg->name), pkg->items,
                     kNoImports);
  }
  for (const VpiUnitScope& at : VpiUnitScopes(*design, object_map_)) {
    MakeNettypeDecls(at.scope, at.unit->cu_items, kNoImports);
  }
}

static std::unordered_set<const RtlirModule*> MarkKeyedTops(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  std::unordered_set<const RtlirModule*> keyed_tops;
  for (auto* top : design->top_modules) {
    if (top == nullptr || top == design->top_modules.front()) continue;
    auto named = objects.find(top->name);
    if (named == objects.end() || named->second == nullptr) continue;
    named->second->top_module = true;
    named->second->type = VpiInstanceKind(top);
    named->second->def_name = std::string(top->name);
    keyed_tops.insert(top);
  }
  return keyed_tops;
}

static std::vector<VpiObject*> UnenclosedObjects(
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  std::vector<VpiObject*> contents;
  for (const auto& [name, object] : objects) {
    if (object != nullptr && object->parent == nullptr && !object->top_module &&
        object->type != vpiPackage) {
      contents.push_back(object);
    }
  }
  return contents;
}

void VpiContext::AttachTopModules(const RtlirDesign* design) {
  if (design == nullptr) return;

  std::unordered_set<const RtlirModule*> keyed_tops =
      MarkKeyedTops(design, object_map_);
  for (auto* top : design->top_modules) {
    if (top == nullptr || keyed_tops.contains(top)) continue;
    std::vector<VpiObject*> contents = UnenclosedObjects(object_map_);

    name_pool_.emplace_back(top->name);
    auto* obj = AllocObject();
    obj->type = VpiInstanceKind(top);
    obj->name = name_pool_.back();
    obj->full_name = std::string(top->name);
    obj->def_name = std::string(top->name);
    obj->top_module = true;
    for (auto* object : contents) {
      object->parent = obj;
      obj->children.push_back(object);
      PrefixFullNamesWithTop(object, obj->name);
    }
    object_map_[obj->name] = obj;
  }
}

void AttachDesignToPliApplications(const RtlirDesign* design, SimContext& ctx) {
  VpiContext& vpi = GetGlobalVpiContext();
  if (vpi.RegisteredSystfs().empty() && vpi.RegisteredCallbacks().empty()) {
    return;
  }
  vpi.SetScheduler(&ctx.GetScheduler());
  vpi.SetSimTimeUnit(static_cast<int>(ctx.GlobalPrecision()));
  vpi.Attach(ctx, design);
  vpi.AttachDesignPorts(design);
  vpi.AttachDesignInterModPaths(design);
}

}  // namespace delta
