#include <string>

#include "elaborator/rtlir.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.28 details 1 and 2: the type parameter object `param` stands as in
// `scope`. A type parameter has no value and so no storage, and nothing else
// makes an object for it.
void MakeTypeParameter(VpiObject* scope, const RtlirParamDecl& param,
                       const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = vpiTypeParameter;
  obj->name = build.keep(std::string(param.name));
  obj->full_name = scope->full_name + "." + std::string(param.name);
  obj->parent = scope;
  obj->local_param = param.is_localparam;
  scope->children.push_back(obj);
}

}  // namespace

void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiAttachBuild& build) {
  // §37.28 details 1 and 2: a value parameter is a vpiParameter, which says
  // through vpiLocalParam whether it is a localparam, and a type parameter is
  // a vpiTypeParameter. A value parameter's storage made it an object stamped
  // vpiReg like any variable, and a type parameter had none, so the
  // vpiParameter iteration found nothing.
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        for (const RtlirParamDecl& param : mod->params) {
          if (param.is_type_param) {
            if (scope != nullptr && param.gen_block_prefix.empty()) {
              MakeTypeParameter(scope, param, build);
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
      });
}

}  // namespace delta
