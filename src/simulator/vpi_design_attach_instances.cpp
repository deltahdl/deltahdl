#include <string>
#include <string_view>

#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

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
                              const SourceManager* sources) {
  obj->time_unit = TimeExponent(mod->timescale.unit, mod->timescale.magnitude);
  obj->time_precision =
      TimeExponent(mod->timescale.precision, mod->timescale.prec_magnitude);
  if (sources == nullptr || !mod->loc.IsValid()) return;
  const SourceLoc kWritten = sources->ResolveToOrigin(mod->loc);
  obj->def_line_no = static_cast<int>(kWritten.line);
  obj->def_file = std::string(sources->FilePath(kWritten.file_id));
}

// §37.10 detail 5: the full names of a package's members begin with the
// package's name followed by "::", where the simulator's keys put a '.'.
void UsePackageSeparator(VpiObject* obj, std::string_view dotted,
                         const std::string& colons) {
  if (obj->full_name.starts_with(dotted)) {
    obj->full_name = colons + obj->full_name.substr(dotted.size());
  }
  for (auto* child : obj->children) UsePackageSeparator(child, dotted, colons);
}

// §37.10: `obj`, the scope the walk made for the package or compilation unit
// named `name`, given the package's type and names.
void MakePackageScope(VpiObject* obj, std::string_view name) {
  obj->type = vpiPackage;
  const std::string kColons = std::string(name) + "::";
  const std::string kDotted = std::string(name) + ".";
  for (auto* member : obj->children) {
    UsePackageSeparator(member, kDotted, kColons);
  }
  obj->full_name = kColons;
}

// §37.10 detail 6: the objects of the compilation unit, which
// vpi_handle_by_name() does not reach.
void MarkInCompilationUnit(VpiObject* obj) {
  obj->in_compilation_unit = true;
  for (auto* child : obj->children) MarkInCompilationUnit(child);
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
    if (pkg == nullptr) continue;
    MakePackageScope(DesignObjectForFlatName(pkg->name), pkg->name);
  }
  // The compilation unit's data is keyed the same way, under "$unit". It is
  // part of no module either, and detail 5 names its objects "$unit::name".
  auto unit = object_map_.find(kUnitScope);
  if (unit == object_map_.end() || unit->second == nullptr) return;
  MakePackageScope(unit->second, kUnitScope);
  MarkInCompilationUnit(unit->second);
}

void VpiContext::AttachInstanceContents(const RtlirDesign* design) {
  AttachInstanceDefinitions(design);
  AttachVariableFacts(design);
  // A continuous assignment's bit select is the bit made here, so the bits
  // come first.
  AttachVectorBits(design);
  AttachContinuousAssignments(design);
}

void VpiContext::AttachInstanceDefinitions(const RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  const SourceManager* sources =
      sim_ctx_ == nullptr ? nullptr : &sim_ctx_->GetDiag().Sources();
  // The first top carries the empty prefix and is keyed under its own name
  // once AttachTopModules has made it.
  const std::string kFirstTop(design->top_modules.front()->name);
  WalkInstancePaths(design,
                    [&](const RtlirModule* mod, const std::string& prefix) {
                      VpiHandle obj = FindObjectForFlatName(
                          object_map_, prefix.empty() ? kFirstTop : prefix);
                      if (obj != nullptr)
                        RecordInstanceDefinition(obj, mod, sources);
                    });
}

}  // namespace delta
