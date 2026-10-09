#include <cstddef>
#include <string>
#include <string_view>
#include <utility>

#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// A unit of a timescale as §37.10 reports it: the power of ten of a second,
// so 10 ns is -8.
int TimeExponent(TimeUnit unit, int magnitude) {
  int exponent = static_cast<int>(unit);
  for (int m = magnitude; m >= 10; m /= 10) ++exponent;
  return exponent;
}

// §37.10: what an instance takes from its definition -- the time unit and
// precision it was elaborated under, and the file and line the definition was
// written on, restated where it came from (detail 8 lets `line move it).
void RecordInstanceDefinition(VpiObject* obj, const RtlirModule* mod,
                              const SourceManager& sources) {
  obj->time_unit = TimeExponent(mod->timescale.unit, mod->timescale.magnitude);
  obj->time_precision =
      TimeExponent(mod->timescale.precision, mod->timescale.prec_magnitude);
  const SourceLoc kWritten = sources.ResolveToOrigin(mod->loc);
  obj->def_line_no = static_cast<int>(kWritten.line);
  obj->def_file = std::string(sources.FilePath(kWritten.file_id));
}

// §37.10: `obj`, the scope the walk made for the package or compilation unit
// named `name`, given the package's type and names. Detail 5 begins each
// member's full name with the package's name followed by "::", where the
// simulator's keys, "pkg.name" (lowerer_package_data.cpp), put a '.'.
void MakePackageScope(VpiObject* obj, std::string_view name) {
  obj->type = vpiPackage;
  const std::string kColons = std::string(name) + "::";
  for (auto* member : obj->children) {
    member->full_name = kColons + std::string(member->name);
  }
  obj->full_name = kColons;
}

// §37.10 detail 6: the objects of the compilation unit, which
// vpi_handle_by_name() does not reach.
void MarkInCompilationUnit(VpiObject* obj) {
  obj->in_compilation_unit = true;
  for (auto* child : obj->children) MarkInCompilationUnit(child);
}

// §37.13 detail 1: the vpiDirection of the io decl a modport port is, the
// direction the modport gave it, and vpiRef for a ref port.
int ModportPortDirection(Direction direction) {
  int declared = vpiNoDirection;
  if (direction == Direction::kInput) declared = vpiInput;
  if (direction == Direction::kOutput) declared = vpiOutput;
  if (direction == Direction::kInout) declared = vpiInout;
  return VpiIoDeclDirection(declared, direction == Direction::kRef,
                            /*expr_is_ref_obj_to_interface_or_modport=*/false,
                            /*expr_is_virtual_interface_var=*/false);
}

// Where the modports of one interface instance are made: the instance, the
// objects keyed under its name `prefix`, among which the names its modports
// write resolve, and what a run builds with.
struct ModportScope {
  VpiObject* iface;
  const VpiObjectMap& objects;
  const std::string& prefix;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

// §37.13 detail 2: what the io decl `io_decl` of the modport port `port`
// reaches through vpiExpr. A port written .port_id(expr) (§25.5.4) reaches the
// expression, and any other the net or variable of the interface it names,
// through a ref obj bound to it when the port is a ref port.
VpiObject* ModportPortExpr(const ModportScope& scope, VpiObject* io_decl,
                           const ModportPort& port) {
  if (port.is_named_port) {
    return VpiInstanceExpression(port.expr, scope.objects, scope.prefix,
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

// §37.7: the modport `decl` declares, under the interface instance, with an io
// decl per port it gives a direction. An imported or exported task or
// function (§25.7) and a clocking block (§25.5.5) a modport names are no io
// decls.
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
    io_decl->direction = ModportPortDirection(port.direction);
    io_decl->io_expr = ModportPortExpr(scope, io_decl, port);
    modport->children.push_back(io_decl);
  }
}

// The scope the lowerer's keys put a compilation unit's data items under
// ("$unit.name", lowerer_package_data.cpp).
constexpr std::string_view kUnitScope = "$unit";

}  // namespace

void VpiContext::AttachInstanceObjects(const RtlirDesign* design) {
  // §37.10: every instance is an object whatever it declares. The scopes
  // DesignObjectForFlatName makes on the way to a declaration are the only
  // instance objects the attach made otherwise, so an instance declaring
  // nothing, and every instance below it, was none.
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [this](const RtlirModule* mod, const std::string& prefix) {
        // §37.6 and §37.9: the instance of an interface or a program is an
        // object of that type, not a module.
        if (!prefix.empty()) {
          DesignObjectForFlatName(prefix)->type = VpiInstanceKind(mod);
        }
      });
}

void VpiContext::AttachPackages(const RtlirDesign* design) {
  // §37.10: a package is an instance of its own, enclosed by no module. Its
  // data is keyed "pkg.name", so the scope the walk made for it is the one
  // the package stands as, and it is given the package's type and names.
  if (design == nullptr) return;
  for (const PackageDecl* pkg : design->packages) {
    MakePackageScope(DesignObjectForFlatName(pkg->name), pkg->name);
  }
  // The compilation unit's data is keyed the same way, under "$unit". It is
  // part of no module either, and detail 5 names its objects "$unit::name".
  auto unit = object_map_.find(kUnitScope);
  if (unit == object_map_.end()) return;
  MakePackageScope(unit->second, kUnitScope);
  MarkInCompilationUnit(unit->second);
}

void VpiContext::AttachInstanceContents(const RtlirDesign* design) {
  AttachInstanceDefinitions(design);
  AttachVariableFacts(design);
  VpiSubroutineObjects subroutines;
  if (design != nullptr) {
    const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                                [this](std::string name) {
                                  name_pool_.push_back(std::move(name));
                                  return std::string_view(name_pool_.back());
                                },
                                sim_ctx_->GetArena()};
    // The scopes the passes below hang a generate block's objects from are
    // the gen scopes this makes.
    AttachGenScopes(design, object_map_, kBuild);
    AttachInstanceArrays(design, object_map_, kBuild);
    AttachClockingBlocks(design, object_map_, *sim_ctx_, kBuild);
    // A continuous assignment's bit select is the bit made here, so the bits
    // come first.
    AttachVectorBits(design, object_map_, *sim_ctx_, kBuild);
    AttachArrayElements(design, object_map_, kBuild);
    AttachStructMembers(design, object_map_, *sim_ctx_, kBuild);
    // A net's bits and members are made while it is still a logic net, the
    // kind both passes above look for, so its own kind comes after them.
    RecordNetObjectKinds(design, object_map_);
    const VpiObjectMap kUnitTypespecs =
        AttachTypespecs(design, object_map_, kBuild);
    AttachParameters(design, object_map_, kUnitTypespecs, kBuild);
    const VpiClassDefnObjects kClasses =
        AttachClassDefinitions(design, object_map_, *sim_ctx_, kBuild);
    // §37.32: the class defn a run's class obj reaches through its typespec,
    // kept per declaration. A class a module declares has one per instance,
    // and ClassDefnOf in vpi_class_objects.cpp takes the one under the
    // instance the object was created in, this one standing for a first top's.
    for (const auto& [key, defn] : kClasses) {
      run_objects_.try_emplace(key.first, defn);
    }
    subroutines = AttachSubroutines(*design, object_map_, *sim_ctx_, kBuild);
    AttachVariableRanges(*design, object_map_, *sim_ctx_, kBuild);
    AttachModports(design, object_map_, *sim_ctx_, kBuild);
    // §37.42: a system call finds the registration its name resolves to, and
    // with it the systf object that registration returned.
    const VpiCallBuild kCalls{
        *sim_ctx_,
        [this](std::string_view name) {
          VpiRegisteredSystf found;
          const s_vpi_systf_data* data =
              ResolveSystf(std::string(name).c_str());
          if (data == nullptr) return found;
          found.type = data->type;
          found.object =
              systf_objects_[static_cast<std::size_t>(data - systfs_.data())];
          return found;
        },
        call_site_objects_,
        stmt_objects_,
        kClasses,
        subroutines,
        kUnitTypespecs};
    AttachProcedures(design, object_map_, kCalls, kBuild);
    AttachPrimitives(
        design, object_map_,
        // Attach made a udp defn for every UDP declaration of the design.
        [this](const UdpDecl* decl) { return run_objects_.at(decl); },
        *sim_ctx_, kBuild);
  }
  AttachContinuousAssignments(design, subroutines);
  AttachGenBlockStorage(design, object_map_);
}

void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build) {
  // §37.7: an interface instance has a modport per modport its interface
  // declares, in the order they were written; none was made, so
  // vpi_iterate(vpiModport, interface) reached nothing.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix, VpiObject* iface) {
        const ModportScope kScope{iface, objects, prefix, ctx, build};
        for (const ModportDecl* decl : mod->modports) {
          MakeModport(kScope, *decl);
        }
      });
}

void VpiContext::AttachInstanceDefinitions(const RtlirDesign* design) {
  const SourceManager& sources = sim_ctx_->GetDiag().Sources();
  // The first top is keyed under its own name once AttachTopModules has made
  // it.
  WalkInstanceObjects(
      design, object_map_,
      [&](const RtlirModule* mod, const std::string& /*prefix*/,
          VpiObject* obj) { RecordInstanceDefinition(obj, mod, sources); });
}

void VpiContext::AttachModuleDefNames(SimContext& sim_ctx) {
  // §38.11's example is what a definition name is for: vpi_handle_by_name
  // reaches an instance and vpi_get_str(vpiDefName, mod) says what it is an
  // instance of, which the example prints for top.mod1. The instance's own
  // name is vpiName and is the answer to a different question, so a module
  // reporting it here said that top.mod1 is an instance of mod1.
  //
  // The run has the answer already: the lowerer records each instance's module
  // type against the instance path, which is the same string the module object
  // carries as its vpiFullName.
  for (auto* obj : all_objects_) {
    // Every kind of instance names its definition (§37.10). A package is no
    // instantiation of anything: AttachPackages types it only after this, and
    // the run records no instance type under its name.
    if (!VpiIsInstanceType(obj->type)) continue;
    std::string_view type = sim_ctx.FindInstanceType(obj->full_name);
    if (!type.empty()) obj->def_name = std::string(type);
  }
}

}  // namespace delta
