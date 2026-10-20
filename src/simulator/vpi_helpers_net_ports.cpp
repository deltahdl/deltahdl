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

// §37.16 details 6 to 8: the ports a net reaches through vpiPorts and
// vpiPortInst. They sit in a file of their own because vpi_helpers_nets.cpp,
// which holds the rest of §37.16, had grown to the length
// .github/workflows/deltahdl.yml admits a source file.

namespace delta {

namespace {

// Where a net stands inside the higher connection of a port: whether the
// connection holds it at all, whether the bit of the connection each of its
// bits lands on can be told, and if so the bit of the connection the net's
// least significant bit lands on, counted from the connection's least
// significant bit. A select starting above the net's bit 0 puts that bit below
// the connection, at a negative place.
struct NetPlace {
  bool held = false;
  bool determinable = true;
  int offset = 0;
};

// The instance an object stands in: the nearest of its holders that is one.
VpiHandle InstanceHolding(VpiHandle obj) {
  for (VpiHandle holder = obj->parent; holder != nullptr;
       holder = holder->parent) {
    if (VpiIsInstanceType(holder->type)) return holder;
  }
  return nullptr;
}

NetPlace PlaceIn(VpiHandle expr, VpiHandle net);

// §11.4.12: a concatenation lays its operands out with the last written at the
// least significant end, so an operand's place is the width of those written
// after it.
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

// Any other operation mixes its operands' bits, so a net it holds lands on no
// bit that can be told.
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
  // A bit of the net puts the net's bit 0 that many places below it; any other
  // select of the net is held without a place that can be told.
  if (expr->type == vpiNetBit) return {true, true, -expr->bit_offset};
  return {true, false, 0};
}

// The port bit of `port` at `offset` places above its least significant bit,
// or the port itself where it is scalar and has none. A port's children are
// its port bits.
VpiHandle PortBitAt(VpiHandle port, int offset) {
  for (VpiHandle bit : port->children) {
    if (bit->bit_offset == offset) return bit;
  }
  return port;
}

// §37.16 details 7 and 8: what `port` gives a vpiPortInst iteration of `ref`,
// whose net `net` its higher connection holds at `place`: the whole port for a
// whole net or an untold place, else the port bit (or scalar port) its bit
// lands on; nothing where none of the net's bits reaches a bit of the port.
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

// What the ports of `instance` whose higher connection holds `net` give a
// vpiPortInst iteration of `ref`.
void CollectInstancePorts(VpiHandle instance, VpiHandle ref, VpiHandle net,
                          std::vector<VpiHandle>& out) {
  for (VpiHandle port : instance->children) {
    if (port->type != kVpiPort || port->high_conn == nullptr) continue;
    const NetPlace kPlace = PlaceIn(port->high_conn, net);
    if (!kPlace.held) continue;
    VpiHandle reached = PortInstOf(port, ref, net, kPlace);
    if (reached != nullptr) out.push_back(reached);
  }
}

// The ports of the instances `scope` holds, reaching into the generate blocks
// it holds but not into the instances, whose ports `ref` stands outside of.
void CollectPortInsts(VpiHandle scope, VpiHandle ref, VpiHandle net,
                      std::vector<VpiHandle>& out) {
  for (VpiHandle child : scope->children) {
    if (child->type == vpiGenScope || child->type == vpiGenScopeArray) {
      CollectPortInsts(child, ref, net, out);
    } else if (VpiIsInstanceType(child->type)) {
      CollectInstancePorts(child, ref, net, out);
    }
  }
}

// §37.16 detail 6: the port bits of `port`, its children, whose lower
// connection is the net bit `bit`.
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
  VpiHandle instance = whole == nullptr ? nullptr : InstanceHolding(whole);
  if (instance != nullptr) CollectPortInsts(instance, net, whole, ports);
  return ports;
}

namespace {

VpiHandle NetBitAt(VpiHandle conn, int place);

// §11.4.12: the net bit `place` bits above the least significant end of the
// concatenation `concat`, its last operand written lowest; null past its
// most significant end.
VpiHandle NetBitInConcatenation(VpiHandle concat, int place) {
  const std::vector<VpiHandle> kOperands = VpiOperationOperands(concat);
  for (VpiHandle operand : std::views::reverse(kOperands)) {
    if (place < operand->size) return NetBitAt(operand, place);
    place -= operand->size;
  }
  return nullptr;
}

// The net bit standing `place` bits above the least significant end of the
// port connection `conn`, or the net standing there whole where it has no
// bits, a scalar net; null where none does or where what does cannot be told:
// a varying bit, a variable, or an operation other than a concatenation.
VpiHandle NetBitAt(VpiHandle conn, int place) {
  if (conn == nullptr) return nullptr;
  if (conn->type == vpiOperation) {
    return conn->op_type == vpiConcatOp ? NetBitInConcatenation(conn, place)
                                        : nullptr;
  }
  if (place >= conn->size || !VpiIsNetsType(conn->type)) return nullptr;
  if (conn->type == vpiNetBit) {
    // A bit a constant index names is the net's own; a varying one is not.
    return VpiBitAtOffset(*conn->parent, conn->bit_offset) == conn ? conn
                                                                   : nullptr;
  }
  VpiHandle bit = VpiBitAtOffset(*conn, place);
  return bit != nullptr ? bit : conn;
}

// Adds to `joined`, once each, what the port `port` joins `bit` to: at each of
// its places where one end holds `bit`, the net bit or scalar net the other
// end holds there.
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
  // §37.16 details 4 and 18: a port joins the bits standing at one place on
  // its two ends, so a bit shares the drivers and loads of the bits joined to
  // it, however many instances apart, and of no other bit of their vectors.
  std::vector<VpiHandle> joined{bit};
  for (std::size_t k = 0; k < joined.size(); ++k) {
    VpiHandle current = joined[k];
    std::vector<VpiHandle> ports = VpiNetPortInsts(current);
    const std::vector<VpiHandle> kOwn = VpiNetPorts(current);
    ports.insert(ports.end(), kOwn.begin(), kOwn.end());
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
  // §37.17 (printed page 1025) draws the port relations from a variable as
  // §37.16 draws them from a net.
  return (VpiIsNetsType(ref->type) || VpiIsVariablesType(ref->type)) &&
         (type == vpiPorts || type == vpiPortInst);
}

std::vector<VpiHandle> VpiTermOrPortObjects(int type, VpiHandle ref) {
  if (ref->type == vpiModPath) return VpiModPathTerms(type, ref);
  if (ref->type == vpiRefObj) return VpiRefObjPorts(type, ref);
  return type == vpiPorts ? VpiNetPorts(ref) : VpiNetPortInsts(ref);
}

}  // namespace delta
