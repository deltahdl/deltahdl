#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The port object `module` holds under `name`, null for none.
VpiObject* PortNamed(VpiHandle module, std::string_view name) {
  for (VpiObject* child : module->children) {
    if (child->type == kVpiPort && child->name == name) return child;
  }
  return nullptr;
}

// §37.14 (figure): the port bits of `port`, one per bit of the net or variable
// it stands for inside the instance, in that object's order and each carrying
// its index and its place in the port's value; the bit is the port bit's
// lowConn. A port whose lower connection has no bits, a scalar one among them,
// has none.
void MakePortBits(VpiObject* port, const VpiAttachBuild& build) {
  if (port->low_conn == nullptr) return;
  for (VpiObject* bit : port->low_conn->children) {
    if (bit->type != vpiNetBit && bit->type != vpiRegBit) continue;
    VpiObject* port_bit = build.alloc();
    port_bit->type = vpiPortBit;
    port_bit->parent = port;
    port_bit->direction = port->direction;
    port_bit->size = 1;
    port_bit->index = bit->index;
    port_bit->index_expr = VpiIntConstant(bit->index, build);
    port_bit->bit_offset = bit->bit_offset;
    port_bit->low_conn = bit;
    port->children.push_back(port_bit);
  }
}

// §37.14 details 3, 4 and 10: the ports of the instance `inst` of the module
// at `prefix` connected - each port's higher connection the expression the
// instantiation wrote for it, its names resolved in the generate blocks and
// the instance holding the instantiation, and its lower connection the
// instance's own net or variable of the port's name. A port the instantiation
// leaves unconnected reaches no higher connection, though the elaborator
// supplies its default, a pull or 'z in its place.
void ConnectPorts(const RtlirModuleInst& inst, const std::string& prefix,
                  const VpiObjectMap& objects, SimContext& ctx,
                  const VpiAttachBuild& build) {
  const std::string kInstance = VpiFlatName(prefix, inst.inst_name);
  VpiHandle module = FindObjectForFlatName(objects, kInstance);
  if (module == nullptr) return;
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    VpiObject* port = PortNamed(module, binding.port_name);
    if (port == nullptr) continue;
    port->high_conn =
        binding.unconnected
            ? nullptr
            : VpiGenBlockExpression(binding.connection,
                                    {objects, prefix, inst.gen_block_prefixes},
                                    ctx, build);
  }
  for (VpiObject* port : module->children) {
    if (port->type != kVpiPort || port->low_conn != nullptr ||
        port->name.empty()) {
      continue;
    }
    port->low_conn =
        FindObjectForFlatName(objects, VpiFlatName(kInstance, port->name));
    MakePortBits(port, build);
  }
}

// The elements of `holder`, one per index of `dims[depth]` in the order it
// declares them, each an interconnect array of the dimensions after it or, of
// the last, an interconnect net.
void FillInterconnectLevel(VpiObject* holder,
                           const std::vector<RtlirUnpackedDim>& dims,
                           std::size_t depth,
                           const std::function<VpiObject*()>& alloc,
                           std::deque<std::string>& names) {
  const RtlirUnpackedDim& dim = dims[depth];
  const bool kLast = depth + 1 == dims.size();
  holder->size = static_cast<int>(dim.Size());
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  for (int64_t index = dim.left;; index += kStep) {
    VpiObject* element = alloc();
    element->type = kLast ? vpiInterconnectNet : vpiInterconnectArray;
    names.push_back(std::string(holder->name) + "[" + std::to_string(index) +
                    "]");
    element->name = names.back();
    element->parent = holder;
    element->index = static_cast<int>(index);
    element->array_member = true;
    holder->children.push_back(element);
    if (!kLast) FillInterconnectLevel(element, dims, depth + 1, alloc, names);
    if (index == dim.right) break;
  }
}

}  // namespace

void VpiMakeInterconnectArray(VpiObject* net, const RtlirPort& port,
                              const std::function<VpiObject*()>& alloc,
                              std::deque<std::string>& names) {
  if (port.num_unpacked_dims == 0 ||
      port.unpacked_dims.size() != port.num_unpacked_dims) {
    return;
  }
  net->type = vpiInterconnectArray;
  FillInterconnectLevel(net, port.unpacked_dims, 0, alloc, names);
}

void AttachPortConnections(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build) {
  // §37.14: a port reaches through vpiHighConn the connection the
  // instantiation makes to it and through vpiLowConn the one inside the
  // instance. Neither was linked but an interconnect port's lower one, so both
  // relations were null for every port of every design. A vector port holds a
  // port bit per bit, which no design had either.
  if (design == nullptr) return;
  WalkInstancePaths(design,
                    [&](const RtlirModule* mod, const std::string& prefix) {
                      for (const RtlirModuleInst& inst : mod->children) {
                        ConnectPorts(inst, prefix, objects, ctx, build);
                      }
                    });
}

}  // namespace delta
