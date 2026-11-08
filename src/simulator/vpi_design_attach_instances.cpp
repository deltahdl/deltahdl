#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/unit_scopes.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_fsms.h"
#include "simulator/vpi_design_attach_interconnects.h"
#include "simulator/vpi_design_attach_interface_tf_decls.h"
#include "simulator/vpi_design_attach_nets.h"
#include "simulator/vpi_design_attach_packed_arrays.h"
#include "simulator/vpi_design_attach_vars.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_instance_facts.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

int TimeExponent(TimeUnit unit, int magnitude) {
  int exponent = static_cast<int>(unit);
  for (int m = magnitude; m >= 10; m /= 10) ++exponent;
  return exponent;
}

int UnconnectedDriveConstant(NetType drive) {
  if (drive == NetType::kTri1) return vpiPull1;
  if (drive == NetType::kTri0) return vpiPull0;
  return vpiHighZ;
}

int DelayModeConstant(DelayModeDirective mode) {
  switch (mode) {
    case DelayModeDirective::kDistributed:
      return vpiDelayModeDistrib;
    case DelayModeDirective::kPath:
      return vpiDelayModePath;
    case DelayModeDirective::kUnit:
      return vpiDelayModeUnit;
    case DelayModeDirective::kZero:
      return vpiDelayModeZero;
    default:
      return vpiDelayModeNone;
  }
}

void RecordInstanceDefinition(VpiObject* obj, const RtlirModule* mod,
                              const ModuleDecl& decl,
                              const SourceManager& sources) {
  obj->automatic = mod->is_automatic;
  VpiInstanceFacts& facts = obj->instance_facts;
  facts.cell = decl.is_cell;
  facts.protected_definition = sources.IsProtected(mod->loc);
  facts.default_net_type = VpiNetTypeConstant(mod->default_nettype);
  facts.unconnected_drive = UnconnectedDriveConstant(mod->unconnected_drive);
  facts.delay_mode = DelayModeConstant(mod->delay_mode);
  obj->def_decay_time = mod->default_decay_time_infinite
                            ? vpiUndefined
                            : static_cast<int>(mod->default_decay_time);
  obj->time_unit = TimeExponent(mod->timescale.unit, mod->timescale.magnitude);
  obj->time_precision =
      TimeExponent(mod->timescale.precision, mod->timescale.prec_magnitude);
  const SourceLoc kWritten = sources.ResolveToOrigin(mod->loc);
  obj->def_line_no = static_cast<int>(kWritten.line);
  obj->def_file = std::string(sources.FilePath(kWritten.file_id));
}

void MakePackageScope(VpiObject* obj, std::string_view name) {
  obj->type = vpiPackage;
  const std::string kColons = std::string(name) + "::";
  for (auto* member : obj->children) {
    member->full_name = kColons + std::string(member->name);
  }
  obj->full_name = kColons;
}

void MarkInCompilationUnit(VpiObject* obj) {
  obj->in_compilation_unit = true;
  for (auto* child : obj->children) MarkInCompilationUnit(child);
}

int ModportPortDirection(Direction direction) {
  int declared = vpiNoDirection;
  if (direction == Direction::kInput) declared = vpiInput;
  if (direction == Direction::kOutput) declared = vpiOutput;
  if (direction == Direction::kInout) declared = vpiInout;
  return VpiIoDeclDirection(declared, direction == Direction::kRef, false,
                            false);
}

struct ModportScope {
  VpiObject* iface;
  const VpiObjectMap& objects;
  const std::string& prefix;
  SimContext& ctx;
  const VpiAttachBuild& build;
  const RtlirNodeAttributes* attrs = nullptr;
  const RtlirModule* mod = nullptr;
};

VpiObject* ModportPortExpr(const ModportScope& scope, VpiObject* io_decl,
                           const ModportPort& port) {
  if (port.is_named_port) {
    static const std::vector<std::string_view> kNoGenBlocks;
    const VpiCallStand kStand{scope.iface, scope.mod};
    return VpiGenBlockExpression(port.expr,
                                 {scope.objects, scope.prefix, kNoGenBlocks,
                                  nullptr, scope.attrs, &kStand},
                                 scope.ctx, scope.build);
  }
  VpiObject* item = FindObjectForFlatName(scope.objects,
                                          VpiFlatName(scope.prefix, port.name));
  if (port.direction != Direction::kRef) return item;
  VpiObject* ref_obj = scope.build.alloc();
  ref_obj->type = vpiRefObj;
  ref_obj->parent = io_decl;
  ref_obj->name = io_decl->name;
  ref_obj->full_name = io_decl->full_name;
  ref_obj->actual = item;
  return ref_obj;
}

void MakeModport(const ModportScope& scope, const ModportDecl& decl) {
  VpiObject* modport = scope.build.alloc();
  modport->type = vpiModport;
  modport->parent = scope.iface;
  modport->name = scope.build.keep(std::string(decl.name));
  modport->full_name = scope.iface->full_name + "." + std::string(decl.name);
  scope.iface->children.push_back(modport);
  for (const ModportPort& port : decl.ports) {
    if (port.is_import || port.is_export || port.is_clocking) continue;
    VpiObject* io_decl = scope.build.alloc();
    io_decl->type = vpiIODecl;
    io_decl->parent = modport;
    io_decl->name = scope.build.keep(std::string(port.name));
    io_decl->full_name = modport->full_name + "." + std::string(port.name);
    io_decl->io_expr = ModportPortExpr(scope, io_decl, port);
    io_decl->direction = ModportPortDirection(port.direction);
    modport->children.push_back(io_decl);
  }
}

constexpr std::string_view kUnitScope = "$unit";

}  // namespace

void VpiContext::AttachInstanceObjects(const RtlirDesign* design) {
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [this](const RtlirModule* mod, const std::string& prefix) {
        if (!prefix.empty()) {
          DesignObjectForFlatName(prefix)->type = VpiInstanceKind(mod);
        }
      });
}

void VpiContext::AttachPackages(const RtlirDesign* design) {
  if (design == nullptr) return;
  for (const PackageDecl* pkg : design->packages) {
    VpiObject* obj = DesignObjectForFlatName(pkg->name);
    MakePackageScope(obj, pkg->name);
    obj->def_name = std::string(pkg->name);
    obj->automatic = pkg->is_automatic;
  }
  for (size_t k = 0; k < design->compilation_units.size(); ++k) {
    VpiObject* own =
        DesignObjectForFlatName(UnitScopes::ScopeName(static_cast<int>(k)));
    own->name = kUnitScope;
    MakePackageScope(own, kUnitScope);
    MarkInCompilationUnit(own);
  }
  if (!design->compilation_units.empty() || design->compilation_unit == nullptr)
    return;
  VpiObject* unit = DesignObjectForFlatName(kUnitScope);
  MakePackageScope(unit, kUnitScope);
  MarkInCompilationUnit(unit);
}

VpiCallBuild VpiContext::CallBuild() {
  return {*sim_ctx_,
          [this](std::string_view name) {
            VpiRegisteredSystf found;
            const s_vpi_systf_data* data =
                ResolveSystf(std::string(name).c_str());
            if (data == nullptr) return found;
            found.type = data->type;
            if (data->type == vpiSysFunc) found.sysfunctype = data->sysfunctype;
            found.object =
                systf_objects_[static_cast<std::size_t>(data - systfs_.data())];
            return found;
          },
          call_site_objects_,
          stmt_objects_,
          call_objects_.classes,
          call_objects_.subroutines,
          call_objects_.unit_typespecs};
}

void VpiContext::AttachInstanceContents(const RtlirDesign* design) {
  AttachInstanceDefinitions(design);
  AttachVariableFacts(design);
  if (design != nullptr) {
    std::vector<VpiDeferredCall> deferred;
    const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                                VpiPoolKeeper(name_pool_), sim_ctx_->GetArena(),
                                &deferred, call_objects_.unit_typespecs};
    AttachGenScopes(design, object_map_, kBuild);
    AttachInstanceArrays(design, object_map_, *sim_ctx_, kBuild);
    AttachClockingBlocks(design, object_map_, *sim_ctx_, kBuild);
    AttachVectorBits(design, object_map_, *sim_ctx_, kBuild);
    AttachArrayElements(design, object_map_, kBuild);
    AttachInterconnects(design, object_map_, *sim_ctx_, kBuild);
    AttachStructMembers(design, object_map_, *sim_ctx_, kBuild);
    RecordNetObjectKinds(design, object_map_);
    RecordNetDeclarationFacts(design, object_map_);
    AttachPackedArrayElements(design, object_map_, *sim_ctx_, kBuild);
    AttachPackedArrayMembers(design, object_map_, *sim_ctx_, kBuild);
    AttachDefaultDisableIffs(design, object_map_, *sim_ctx_, kBuild);
    AttachAliasStatements(design, object_map_, *sim_ctx_, kBuild);
    call_objects_.classes = AttachClassDefinitions(
        design, object_map_, *sim_ctx_, kBuild, call_objects_.class_sites);
    for (const auto& [key, defn] : call_objects_.classes) {
      run_objects_.try_emplace(key.first, defn);
    }
    call_objects_.unit_typespecs = AttachTypespecs(
        design, object_map_, call_objects_.classes, *sim_ctx_, kBuild);
    AttachParameters(design, object_map_, call_objects_.unit_typespecs,
                     *sim_ctx_, kBuild);
    AttachFsms(design, object_map_, *sim_ctx_, kBuild);
    AttachAttributes(design, object_map_, *sim_ctx_, kBuild);
    call_objects_.design = design;
    AttachClassVarTypespecs(design, object_map_, call_objects_.classes,
                            *sim_ctx_, kBuild);
    call_objects_.subroutines =
        AttachSubroutines(*design, object_map_, *sim_ctx_, kBuild);
    AttachVariableAndNetRanges(*design, object_map_, *sim_ctx_, kBuild);
    AttachVariableInitializers(*design, object_map_, *sim_ctx_, kBuild);
    AttachModports(design, object_map_, *sim_ctx_, kBuild);
    AttachInterfaceTfDecls(design, object_map_, call_objects_.subroutines,
                           *sim_ctx_, kBuild);
    const VpiCallBuild kCalls = CallBuild();
    VpiAttachPackageAndUnitLets(*design, object_map_, *sim_ctx_, kBuild);
    AttachPackageAssertionItemDecls(
        *design, object_map_, call_objects_.unit_typespecs, *sim_ctx_, kBuild);
    AttachProcedures(design, object_map_, kCalls, kBuild);
    AttachPrimitives(
        design, object_map_,
        [this](const UdpDecl* decl) { return run_objects_.at(decl); },
        *sim_ctx_, kBuild);
    AttachContinuousAssignments(design, kCalls);
    VpiShapeDeferredCalls(design, object_map_, deferred, kCalls, kBuild);
  }
  AttachGenBlockStorage(design, object_map_);
  AttachGenBlockInstances(design, object_map_, VpiPoolKeeper(name_pool_));
}

void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix, VpiObject* iface) {
        const ModportScope kScope{iface, objects,          prefix, ctx,
                                  build, &mod->node_attrs, mod};
        for (const ModportDecl* decl : mod->modports) {
          MakeModport(kScope, *decl);
        }
      });
}

void VpiContext::AttachInstanceDefinitions(const RtlirDesign* design) {
  const SourceManager& sources = sim_ctx_->GetDiag().Sources();
  WalkInstanceObjects(
      design, object_map_,
      [&](const RtlirModule* mod, const std::string&, VpiObject* obj) {
        RecordInstanceDefinition(obj, mod, VpiDeclOf(*mod), sources);
      });
}

void VpiContext::AttachModuleDefNames(SimContext& sim_ctx) {
  for (auto* obj : all_objects_) {
    if (!VpiIsInstanceType(obj->type)) continue;
    std::string_view type = sim_ctx.FindInstanceType(obj->full_name);
    if (!type.empty()) obj->def_name = std::string(type);
    std::string_view binding = sim_ctx.FindInstanceBinding(obj->full_name);
    if (const std::size_t kDot = binding.find('.');
        kDot != std::string_view::npos) {
      obj->library_name = std::string(binding.substr(0, kDot));
      obj->cell_name = std::string(binding.substr(kDot + 1));
    }
    obj->config_name = std::string(sim_ctx.FindInstanceConfig(obj->full_name));
  }
}

}  // namespace delta
