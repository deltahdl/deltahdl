#include <algorithm>
#include <cstddef>
#include <ranges>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct NetPlace {
  bool held = false;
  bool determinable = true;
  int offset = 0;
};

VpiHandle InstanceHolding(VpiHandle obj) {
  for (VpiHandle holder = obj->parent; holder != nullptr;
       holder = holder->parent) {
    if (VpiIsInstanceType(holder->type)) return holder;
  }
  return nullptr;
}

NetPlace PlaceIn(VpiHandle expr, VpiHandle net);

NetPlace PlaceInConcatenation(VpiHandle concat, VpiHandle net) {
  int below = 0;
  const std::vector<VpiHandle> kOperands = VpiOperationOperands(concat);
  for (VpiHandle operand : std::views::reverse(kOperands)) {
    NetPlace place = PlaceIn(operand, net);
    if (place.held) {
      place.offset += below;
      return place;
    }
    below += operand->size;
  }
  return {};
}

NetPlace PlaceInOperation(VpiHandle operation, VpiHandle net) {
  if (operation->op_type == vpiConcatOp) {
    return PlaceInConcatenation(operation, net);
  }
  for (VpiHandle operand : VpiOperationOperands(operation)) {
    if (PlaceIn(operand, net).held) return {true, false, 0};
  }
  return {};
}

NetPlace PlaceIn(VpiHandle expr, VpiHandle net) {
  if (expr == net) return {true, true, 0};
  if (expr->type == vpiOperation) return PlaceInOperation(expr, net);
  if (expr->parent != net) return {};
  if (expr->type == vpiNetBit) return {true, true, -expr->bit_offset};
  return {true, false, 0};
}

VpiHandle PortBitAt(VpiHandle port, int offset) {
  for (VpiHandle bit : port->children) {
    if (bit->bit_offset == offset) return bit;
  }
  return port;
}

VpiHandle PortInstOf(VpiHandle port, VpiHandle ref, VpiHandle net,
                     const NetPlace& place) {
  const bool kBit = ref->type == vpiNetBit;
  const int kFirst = place.offset + (kBit ? ref->bit_offset : 0);
  const int kCount = kBit ? 1 : net->size;
  const bool kConnected =
      !place.determinable || (kFirst < port->size && kFirst + kCount > 0);
  if (!VpiPortInstReferenceQualifies(kConnected)) return nullptr;
  const bool kBitOrScalar =
      kBit || (net->type != vpiNetArray && net->size == 1);
  if (VpiPortInstReferenceGranularity(kBitOrScalar, !kBitOrScalar,
                                      !place.determinable) ==
      VpiPortGranularity::kEntirePort) {
    return port;
  }
  return PortBitAt(port, kFirst);
}

VpiHandle NetBitAt(VpiHandle conn, int place);

VpiHandle NetBitInConcatenation(VpiHandle concat, int place) {
  const std::vector<VpiHandle> kOperands = VpiOperationOperands(concat);
  for (VpiHandle operand : std::views::reverse(kOperands)) {
    if (place < operand->size) return NetBitAt(operand, place);
    place -= operand->size;
  }
  return nullptr;
}

VpiHandle NetBitAt(VpiHandle conn, int place) {
  if (conn == nullptr) return nullptr;
  if (conn->type == vpiOperation) {
    return conn->op_type == vpiConcatOp ? NetBitInConcatenation(conn, place)
                                        : nullptr;
  }
  if (place >= conn->size || !VpiIsNetsType(conn->type)) return nullptr;
  if (conn->type == vpiNetBit) {
    return VpiBitAtOffset(*conn->parent, conn->bit_offset) == conn ? conn
                                                                   : nullptr;
  }
  VpiHandle bit = VpiBitAtOffset(*conn, place);
  return bit != nullptr ? bit : conn;
}

NetPlace PlaceOfReference(VpiHandle port, VpiHandle ref, VpiHandle net) {
  if (ref->type == vpiNetBit) {
    for (int place = 0; place < port->size; ++place) {
      if (NetBitAt(port->high_conn, place) == ref) {
        return {true, true, place - ref->bit_offset};
      }
    }
  }
  return PlaceIn(port->high_conn, net);
}

void CollectInstancePorts(VpiHandle instance, VpiHandle ref, VpiHandle net,
                          std::vector<VpiHandle>& out) {
  for (VpiHandle port : instance->children) {
    if (port->type != kVpiPort || port->high_conn == nullptr) continue;
    const NetPlace kPlace = PlaceOfReference(port, ref, net);
    if (!kPlace.held) continue;
    VpiHandle reached = PortInstOf(port, ref, net, kPlace);
    if (reached != nullptr) out.push_back(reached);
  }
}

void CollectHeldInstances(VpiHandle scope, std::vector<VpiHandle>& out) {
  for (VpiHandle child : scope->children) {
    if (child->type == vpiGenScope || child->type == vpiGenScopeArray) {
      CollectHeldInstances(child, out);
    } else if (VpiIsInstanceType(child->type)) {
      out.push_back(child);
    }
  }
}

std::vector<VpiHandle> InstancesBeside(VpiHandle net) {
  VpiHandle whole = net->type == vpiNetBit ? net->parent : net;
  std::vector<VpiHandle> held;
  VpiHandle instance = whole == nullptr ? nullptr : InstanceHolding(whole);
  if (instance != nullptr) CollectHeldInstances(instance, held);
  return held;
}

void CollectPortBitsOf(VpiHandle port, VpiHandle bit,
                       std::vector<VpiHandle>& out) {
  for (VpiHandle port_bit : port->children) {
    if (port_bit->low_conn == bit) out.push_back(port_bit);
  }
}

}  // namespace

std::vector<VpiHandle> VpiNetPorts(VpiHandle net) {
  const bool kBits =
      VpiPortsReferenceGranularity(net->type) == VpiPortGranularity::kPortBits;
  VpiHandle whole = kBits ? net->parent : net;
  std::vector<VpiHandle> ports;
  VpiHandle instance = whole == nullptr ? nullptr : InstanceHolding(whole);
  if (instance == nullptr) return ports;
  for (VpiHandle port : instance->children) {
    if (port->type != kVpiPort || port->low_conn != whole) continue;
    if (kBits) {
      CollectPortBitsOf(port, net, ports);
    } else {
      ports.push_back(port);
    }
  }
  return ports;
}

std::vector<VpiHandle> VpiNetPortInsts(VpiHandle net) {
  VpiHandle whole = net->type == vpiNetBit ? net->parent : net;
  std::vector<VpiHandle> ports;
  for (VpiHandle instance : InstancesBeside(net)) {
    CollectInstancePorts(instance, net, whole, ports);
  }
  return ports;
}

namespace {

void AddBitsJoinedAcross(VpiHandle port, VpiHandle bit,
                         std::vector<VpiHandle>& joined) {
  for (int place = 0; place < port->size; ++place) {
    VpiHandle high = NetBitAt(port->high_conn, place);
    VpiHandle low = NetBitAt(port->low_conn, place);
    VpiHandle far = high == bit ? low : (low == bit ? high : nullptr);
    if (far != nullptr && std::ranges::find(joined, far) == joined.end()) {
      joined.push_back(far);
    }
  }
}

}  // namespace

std::vector<VpiHandle> VpiNetBitsJoinedThroughPorts(VpiHandle bit) {
  std::vector<VpiHandle> joined{bit};
  for (std::size_t k = 0; k < joined.size(); ++k) {
    VpiHandle current = joined[k];
    std::vector<VpiHandle> ports = VpiNetPorts(current);
    for (VpiHandle instance : InstancesBeside(current)) {
      for (VpiHandle port : instance->children) {
        if (port->type == kVpiPort) ports.push_back(port);
      }
    }
    for (VpiHandle port : ports) {
      AddBitsJoinedAcross(port->type == vpiPortBit ? port->parent : port,
                          current, joined);
    }
  }
  return joined;
}

bool VpiIsTermOrPortRelation(int type, VpiHandle ref) {
  if (ref->type == vpiModPath) {
    return type == vpiModPathIn || type == vpiModPathOut ||
           type == vpiModDataPathIn;
  }
  if (ref->type == vpiRefObj) return VpiIsRefObjPortRelation(type);
  return (VpiIsNetsType(ref->type) || VpiIsVariablesType(ref->type)) &&
         (type == vpiPorts || type == vpiPortInst);
}

std::vector<VpiHandle> VpiTermOrPortObjects(int type, VpiHandle ref) {
  if (ref->type == vpiModPath) return VpiModPathTerms(type, ref);
  if (ref->type == vpiRefObj) return VpiRefObjPorts(type, ref);
  return type == vpiPorts ? VpiNetPorts(ref) : VpiNetPortInsts(ref);
}

}  // namespace delta
