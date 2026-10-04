#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
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
// or the compilation unit `unit` declares; and for a type no typedef names, a
// typespec of its kind. Null for a type neither gives one.
VpiObject* TypeParameterTypespec(const DataType& type, VpiObject* scope,
                                 const VpiObject* unit,
                                 const VpiAttachBuild& build) {
  if (type.kind == DataTypeKind::kNamed) {
    for (const VpiObject* at = scope; at != nullptr; at = at->parent) {
      if (VpiObject* found = TypespecNamed(*at, type.type_name)) return found;
    }
    return unit == nullptr ? nullptr : TypespecNamed(*unit, type.type_name);
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
                       const VpiObject* unit, const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = vpiTypeParameter;
  obj->name = build.keep(std::string(param.name));
  obj->full_name = scope->full_name + "." + std::string(param.name);
  obj->parent = scope;
  obj->local_param = param.is_localparam;
  if (param.resolved_type != nullptr) {
    obj->param_typespec =
        TypeParameterTypespec(*param.resolved_type, scope, unit, build);
  }
  scope->children.push_back(obj);
}

// The parameters of the instance at `prefix`, an instance of `mod`, each made
// the kind of parameter object it is; `unit` is the compilation unit's scope.
void AttachScopeParameters(const RtlirModule* mod, const std::string& prefix,
                           const VpiObjectMap& objects, const VpiObject* unit,
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

}  // namespace

void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiAttachBuild& build) {
  // §37.28 details 1 and 2: a value parameter is a vpiParameter, which says
  // through vpiLocalParam whether it is a localparam, and a type parameter is
  // a vpiTypeParameter whose vpiTypespec is the typespec of its type. A value
  // parameter's storage made it an object stamped vpiReg like any variable,
  // and a type parameter had none, so the vpiParameter iteration found nothing
  // and no type parameter reached a typespec.
  if (design == nullptr) return;
  auto unit = objects.find("$unit");
  const VpiObject* unit_scope = unit == objects.end() ? nullptr : unit->second;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        AttachScopeParameters(mod, prefix, objects, unit_scope, build);
      });
}

}  // namespace delta
