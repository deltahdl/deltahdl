#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// The port object `module` holds under `name`, null for none.
VpiObject* PortNamed(VpiHandle module, std::string_view name) {
  for (VpiObject* child : module->children) {
    if (child->type == kVpiPort && child->name == name) return child;
  }
  return nullptr;
}

// §37.14 details 3, 4 and 10: the ports of the instance `inst` of the module
// at `prefix` connected - each port's higher connection the expression the
// instantiation wrote for it, its names resolved in the instance holding the
// instantiation, and its lower connection the instance's own net or variable
// of the port's name. A port the instantiation leaves unconnected reaches no
// higher connection, though the elaborator supplies its default, a pull or 'z
// in its place.
void ConnectPorts(const RtlirModuleInst& inst, const std::string& prefix,
                  const VpiObjectMap& objects, SimContext& ctx,
                  const VpiAttachBuild& build) {
  const std::string kInstance = VpiFlatName(prefix, inst.inst_name);
  VpiHandle module = FindObjectForFlatName(objects, kInstance);
  if (module == nullptr) return;
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    VpiObject* port = PortNamed(module, binding.port_name);
    if (port == nullptr) continue;
    port->high_conn = binding.unconnected
                          ? nullptr
                          : VpiInstanceExpression(binding.connection, objects,
                                                  prefix, ctx, build);
  }
  for (VpiObject* port : module->children) {
    if (port->type != kVpiPort || port->low_conn != nullptr ||
        port->name.empty()) {
      continue;
    }
    port->low_conn =
        FindObjectForFlatName(objects, VpiFlatName(kInstance, port->name));
  }
}

}  // namespace

void AttachPortConnections(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build) {
  // §37.14: a port reaches through vpiHighConn the connection the
  // instantiation makes to it and through vpiLowConn the one inside the
  // instance. Neither was linked but an interconnect port's lower one, so both
  // relations were null for every port of every design.
  if (design == nullptr) return;
  WalkInstancePaths(design,
                    [&](const RtlirModule* mod, const std::string& prefix) {
                      for (const RtlirModuleInst& inst : mod->children) {
                        ConnectPorts(inst, prefix, objects, ctx, build);
                      }
                    });
}

}  // namespace delta
