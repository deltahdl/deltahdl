#include <algorithm>
#include <cstddef>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
#include "simulator/vpi_user.h"

namespace delta {

// ===========================================================================
// §37.46 Net drivers and loads.
// ===========================================================================

bool VpiIsPortsType(int type) {
  // §37.46 (figure): the `ports` enclosure inside both the net drivers and the
  // net loads classes is dotted, so §37.4.1 makes it a class - a grouping of
  // further objects and classes that is never an object itself. §37.14 draws a
  // port and a port bit inside it, and §37.4.1 has a relation drawn to a class
  // reach the kinds the class groups, so both are what the two edges mean by a
  // port.
  return type == vpiPort || type == vpiPortBit;
}

bool VpiIsNetDriverType(int type) {
  // §37.46 (figure, net drivers): a port, a force, a delay terminal, a
  // continuous assignment (whole or single bit), or a primitive terminal.
  // Unlike a variable (§37.21) a net is not driven by a procedural assignment
  // statement.
  //
  // The ports enclosure was read as the single kind vpiPort, so a port bit
  // driving a net was a driver to nothing.
  if (VpiIsPortsType(type)) return true;
  switch (type) {
    case vpiForce:
    case vpiDelayTerm:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiPrimTerm:
      return true;
    default:
      return false;
  }
}

bool VpiIsNetLoadType(int type) {
  // §37.46 (figure, net loads): a delay terminal, an assignment statement, a
  // force, a continuous assignment (whole or single bit), or a primitive
  // terminal. A port is excluded here; detail 1 governs when a port is a load.
  switch (type) {
    case vpiDelayTerm:
    case vpiAssignStmt:
    case vpiForce:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiPrimTerm:
      return true;
    default:
      return false;
  }
}

namespace {

// §37.46 detail 1: whether the operation `expr` is a concatenation. The
// operand connections it groups drive/load their nets individually, so a
// concatenation on a port does not make the whole port a complex-expression
// load.
bool VpiIsConcatenationExpression(const VpiObject* expr) {
  return expr->op_type == vpiConcatOp || expr->op_type == vpiMultiConcatOp;
}

// A force and a continuous assignment drive what their target writes and load
// what their expression reads, the one without the other unless the net
// stands on both sides. Of a net bit, a side holds the bit where it uses it
// (§37.58 detail 2), through the bit, its vector or a select holding it, the
// target writing into that vector rather than only reading an index there.
bool AssignmentDrivesOrLoads(const VpiObject& assign, const VpiObject& net,
                             bool want_driver) {
  if (net.type != vpiNetBit || net.parent == nullptr) {
    return want_driver ? VpiAssignTargetWrites(assign.lhs, net)
                       : VpiExpressionReads(assign.rhs, net);
  }
  return want_driver ? VpiAssignTargetWrites(assign.lhs, *net.parent) &&
                           VpiExpressionUses(assign.lhs, net)
                     : VpiExpressionUses(assign.rhs, net);
}

}  // namespace

bool VpiIsNetDriverOrLoad(VpiHandle child, VpiHandle net, bool want_driver) {
  if (child->type == vpiPrimTerm) {
    return child->direction == kVpiInout ||
           child->direction == (want_driver ? kVpiOutput : kVpiInput);
  }
  if (child->type == vpiForce || child->type == vpiContAssign) {
    return AssignmentDrivesOrLoads(*child, *net, want_driver);
  }
  // §37.45 details 1 and 2: of the two terms a delay device places on a net,
  // the input term takes the value the net's drivers give and the output term
  // passes it on to its loads once the delay has passed, so the one is a load
  // of the net and the other a driver.
  if (child->type == vpiDelayTerm && child->parent != nullptr &&
      child->parent->type == vpiDelayDevice) {
    return (child->parent->out_term == child) == want_driver;
  }
  if (VpiIsPortsType(child->type)) {
    return VpiPortIsComplexExpressionLoad(child) != want_driver;
  }
  return want_driver ? VpiIsNetDriverType(child->type)
                     : VpiIsNetLoadType(child->type);
}

namespace {

// §37.16 detail 16: whether the connection `conn` on one end of a port is
// driven by nets alone, or by nothing: a net, a bit or a select of one (what
// stands in a net), or a concatenation of such, each of whose nets drives its
// own bits. A variable, a constant or any other operation drives the port as
// something else.
bool DrivenByNets(VpiHandle conn) {
  if (conn == nullptr || VpiIsNetsType(conn->type)) return true;
  if (conn->type == vpiOperation) {
    return VpiIsConcatenationExpression(conn) &&
           std::ranges::all_of(VpiOperationOperands(conn), DrivenByNets);
  }
  return conn->parent != nullptr && VpiIsNetsType(conn->parent->type);
}

// Whether a port of direction `direction` passes values into the module it is
// a port of (`inward`) or out of it: an inout port both ways.
bool PassesValues(int direction, bool inward) {
  return direction == vpiInout || direction == (inward ? vpiInput : vpiOutput);
}

}  // namespace

std::vector<VpiHandle> VpiNetPortDrivers(VpiHandle net) {
  // §37.16 detail 16: an output or inout port of an instance the net's own
  // instance holds drives it from its lower connection, and an input or
  // inout port of the net's own instance from its higher connection. Driven
  // by a net there, the port passes that net's drivers on rather than being a
  // driver itself.
  std::vector<VpiHandle> ports;
  for (VpiHandle port : VpiNetPortInsts(net)) {
    if (PassesValues(port->direction, false) && !DrivenByNets(port->low_conn)) {
      ports.push_back(port);
    }
  }
  for (VpiHandle port : VpiNetPorts(net)) {
    if (PassesValues(port->direction, true) && !DrivenByNets(port->high_conn)) {
      ports.push_back(port);
    }
  }
  return ports;
}

namespace {

// The nets the connection `conn`, driven by nets alone, names: a net, the net
// a bit or a select of one stands in, or those of a concatenation's operands.
void NetsNamedIn(VpiHandle conn, std::vector<VpiHandle>& out) {
  if (conn == nullptr) return;
  if (conn->type == vpiOperation) {
    for (VpiHandle operand : VpiOperationOperands(conn)) {
      NetsNamedIn(operand, out);
    }
    return;
  }
  const bool kPart = conn->type == vpiNetBit || !VpiIsNetsType(conn->type);
  VpiHandle net = kPart ? conn->parent : conn;
  if (std::ranges::find(out, net) == out.end()) out.push_back(net);
}

// Adds to `joined`, once each, the nets on the far end of each port nets drive
// at both ends that `net` stands on one end of.
void AddNetsJoinedTo(VpiHandle net, std::vector<VpiHandle>& joined) {
  for (VpiHandle port : VpiNetPortInsts(net)) {
    if (DrivenByNets(port->high_conn) && DrivenByNets(port->low_conn)) {
      NetsNamedIn(port->low_conn, joined);
    }
  }
  for (VpiHandle port : VpiNetPorts(net)) {
    if (DrivenByNets(port->high_conn)) NetsNamedIn(port->high_conn, joined);
  }
}

}  // namespace

std::vector<VpiHandle> VpiNetsJoinedThroughPorts(VpiHandle net) {
  // §37.16 details 4 and 16: a port nets drive at both ends passes the drivers
  // and loads of the nets on either end to the other, so the nets it connects
  // share them, however many instances apart.
  std::vector<VpiHandle> joined{net};
  for (std::size_t k = 0; k < joined.size(); ++k) {
    AddNetsJoinedTo(joined[k], joined);
  }
  return joined;
}

std::vector<VpiHandle> VpiNetLocalPorts(VpiHandle net, bool want_driver) {
  // §37.16 detail 17: the ports of the instance holding the net that connect
  // to it are among its local drivers and loads, an input port a driver, an
  // output port a load and an inout port both.
  std::vector<VpiHandle> ports;
  for (VpiHandle port : VpiNetPorts(net)) {
    if (PassesValues(port->direction, want_driver)) ports.push_back(port);
  }
  return ports;
}

namespace {

// §37.45: the drivers or loads of the net `net` a delay term `term` placed on
// it reaches, less the two terms of its own device, which stand between them.
void CollectAroundDelayTerm(VpiHandle term, VpiHandle net, bool want_driver,
                            std::vector<VpiHandle>& found) {
  for (VpiHandle child : net->children) {
    if (child->parent != term->parent &&
        VpiIsNetDriverOrLoad(child, net, want_driver)) {
      found.push_back(child);
    }
  }
}

// The drivers or loads the net `net` holds, with the ports detail 17 (`local`)
// or detail 16 adds to them.
void CollectOfOneNet(VpiHandle net, bool want_driver, bool local,
                     std::vector<VpiHandle>& found) {
  for (VpiHandle child : net->children) {
    if (VpiIsNetDriverOrLoad(child, net, want_driver)) found.push_back(child);
  }
  std::vector<VpiHandle> ports;
  if (local) {
    ports = VpiNetLocalPorts(net, want_driver);
  } else if (want_driver) {
    ports = VpiNetPortDrivers(net);
  }
  found.insert(found.end(), ports.begin(), ports.end());
}

// §37.16 detail 18: a net bit's forces and continuous assignments hang on its
// vector, and the bit is driven or loaded by those writing or reading it.
void CollectBitAssignments(VpiHandle bit, bool want_driver,
                           std::vector<VpiHandle>& found) {
  if (bit->parent == nullptr) return;
  for (VpiHandle child : bit->parent->children) {
    if ((child->type == vpiForce || child->type == vpiContAssign) &&
        VpiIsNetDriverOrLoad(child, bit, want_driver)) {
      found.push_back(child);
    }
  }
}

// The nets whose drivers and loads those of `net` take in: `net` alone for the
// local relations (§37.16 detail 17), and otherwise each net, or of a net bit
// each bit, a port joins to it (details 4 and 18).
std::vector<VpiHandle> NetsSharingRelations(VpiHandle net, bool local) {
  if (local) return {net};
  return net->type == vpiNetBit ? VpiNetBitsJoinedThroughPorts(net)
                                : VpiNetsJoinedThroughPorts(net);
}

}  // namespace

std::vector<VpiHandle> VpiNetDriversOrLoads(VpiHandle node, bool want_driver,
                                            bool local) {
  std::vector<VpiHandle> found;
  VpiHandle net = node->term_net != nullptr ? node->term_net : node;
  // §37.16 detail 11: a part of a nettype net has no driver iteration.
  if (want_driver && !VpiNetDriverIterationSupported(VpiNetTypeOf(net))) {
    return found;
  }
  if (net != node) {
    CollectAroundDelayTerm(node, net, want_driver, found);
    return found;
  }
  for (VpiHandle joined : NetsSharingRelations(net, local)) {
    CollectOfOneNet(joined, want_driver, local, found);
    if (joined->type == vpiNetBit) {
      CollectBitAssignments(joined, want_driver, found);
    }
  }
  std::vector<VpiHandle> unique;
  for (VpiHandle object : found) {
    if (std::ranges::find(unique, object) == unique.end()) {
      unique.push_back(object);
    }
  }
  return unique;
}

void VpiHangOnNetsNamed(VpiHandle holder, VpiHandle expr) {
  if (expr == nullptr) return;
  VpiObject* net = VpiIsNetsType(expr->type) ? expr : nullptr;
  if (expr->type == vpiNetBit) net = expr->parent;
  if (net != nullptr) {
    if (std::ranges::find(net->children, holder) == net->children.end()) {
      net->children.push_back(holder);
    }
    return;
  }
  if (expr->type != vpiOperation) return;
  for (VpiObject* operand : expr->children) VpiHangOnNetsNamed(holder, operand);
}

bool VpiPortIsComplexExpressionLoad(VpiHandle port) {
  // §37.46 detail 1: a complex expression on an input port - an operation other
  // than a concatenation - loads the nets it reads, and the port is then the
  // load object reported when iterating the net's loads. A simple reference is
  // a direct connection rather than a complex-expression load, a
  // concatenation's operands connect their nets individually, and only an input
  // port loads this way. The complex expression itself is reached through
  // vpiHighConn (§37.14).
  if (port->direction != vpiInput) return false;
  VpiObject* expr = port->high_conn;
  if (!expr || expr->type != vpiOperation) return false;
  return !VpiIsConcatenationExpression(expr);
}

}  // namespace delta
