#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The typespec `scope` declares under `name`, or null.
VpiObject* TypespecNamed(const VpiObject& scope, std::string_view name) {
  for (VpiObject* child : scope.children) {
    if (child != nullptr && child->type != vpiTypeParameter &&
        VpiIsTypespecType(child->type) && child->name == name) {
      return child;
    }
  }
  return nullptr;
}

// §37.28 detail 2: the typespec of `type`, the type a type parameter of
// `scope` has at the end of elaboration, its typedef aliases left unresolved:
// for a typedef's name, the typespec of the typedef, which `scope`, an
// instance enclosing it, where a parameter value assignment naming it stands,
// or the compilation unit, whose typespecs are `unit`, declares; and for a
// type no typedef names, a typespec of its kind. Null for a type neither gives
// one.
VpiObject* TypeParameterTypespec(const DataType& type, VpiObject* scope,
                                 const VpiObjectMap& unit,
                                 const VpiAttachBuild& build) {
  if (type.kind == DataTypeKind::kNamed) {
    for (const VpiObject* at = scope; at != nullptr; at = at->parent) {
      if (VpiObject* found = TypespecNamed(*at, type.type_name)) return found;
    }
    auto in_unit = unit.find(type.type_name);
    return in_unit == unit.end() ? nullptr : in_unit->second;
  }
  const int kKind = VpiTypespecKind(type.kind);
  if (kKind == 0) return nullptr;
  VpiObject* typespec = build.alloc();
  typespec->type = kKind;
  return typespec;
}

// §37.28 details 1 and 2: the type parameter object `param` stands as in
// `scope`, related through vpiTypespec to the type it has. A type parameter
// has no value and so no storage, and nothing else makes an object for it.
void MakeTypeParameter(VpiObject* scope, const RtlirParamDecl& param,
                       const VpiObjectMap& unit, const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = vpiTypeParameter;
  obj->name = build.keep(std::string(param.name));
  obj->full_name = VpiScopedFullName(scope, param.name);
  obj->parent = scope;
  obj->local_param = param.is_localparam;
  if (param.resolved_type != nullptr) {
    obj->param_typespec =
        TypeParameterTypespec(*param.resolved_type, scope, unit, build);
  }
  scope->children.push_back(obj);
}

// The parameters of the instance at `prefix`, an instance of `mod`, each made
// the kind of parameter object it is; `unit` holds the compilation unit's
// typespecs.
void AttachScopeParameters(const RtlirModule* mod, const std::string& prefix,
                           const VpiObjectMap& objects,
                           const VpiObjectMap& unit,
                           const VpiAttachBuild& build) {
  VpiObject* scope = FindObjectForFlatName(
      objects, prefix.empty() ? std::string(mod->name) : prefix);
  for (const RtlirParamDecl& param : mod->params) {
    if (param.is_type_param) {
      if (scope != nullptr && param.gen_block_prefix.empty()) {
        MakeTypeParameter(scope, param, unit, build);
      }
      continue;
    }
    VpiObject* obj = FindObjectForFlatName(
        objects, VpiFlatName(prefix, std::string(param.gen_block_prefix) +
                                         std::string(param.name)));
    if (obj == nullptr) continue;
    obj->type = vpiParameter;
    obj->local_param = param.is_localparam;
  }
}

// §37.10 with §37.28: the parameters the package `pkg` declares, in `scope`,
// the package it stands as: a value parameter's object, which its storage
// made, made a vpiParameter, and a type parameter given one of its own. Each
// is a local parameter, since §6.20.4 makes a `parameter` written in a
// package mean `localparam`.
void AttachPackageParameters(const PackageDecl& pkg, VpiObject& scope,
                             const VpiObjectMap& unit,
                             const VpiAttachBuild& build) {
  for (const ModuleItem* item : pkg.items) {
    if (item == nullptr || item->kind != ModuleItemKind::kParamDecl) continue;
    if (item->data_type.kind == DataTypeKind::kVoid) {
      RtlirParamDecl param;
      param.name = item->name;
      param.is_localparam = true;
      param.is_type_param = true;
      param.resolved_type = &item->typedef_type;
      MakeTypeParameter(&scope, param, unit, build);
      continue;
    }
    for (VpiObject* child : scope.children) {
      if (child->name == item->name && !VpiIsTypespecType(child->type)) {
        child->type = vpiParameter;
        child->local_param = true;
      }
    }
  }
}

}  // namespace

void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiObjectMap& unit_typespecs,
                      const VpiAttachBuild& build) {
  // §37.28 details 1 and 2: a value parameter is a vpiParameter, which says
  // through vpiLocalParam whether it is a localparam, and a type parameter is
  // a vpiTypeParameter whose vpiTypespec is the typespec of its type. A value
  // parameter's storage made it an object stamped vpiReg like any variable,
  // and a type parameter had none, so the vpiParameter iteration found nothing
  // and no type parameter reached a typespec.
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        AttachScopeParameters(mod, prefix, objects, unit_typespecs, build);
      });
  for (const PackageDecl* pkg : design->packages) {
    if (pkg == nullptr) continue;
    VpiObject* scope = FindObjectForFlatName(objects, pkg->name);
    if (scope != nullptr) {
      AttachPackageParameters(*pkg, *scope, unit_typespecs, build);
    }
  }
}

}  // namespace delta
