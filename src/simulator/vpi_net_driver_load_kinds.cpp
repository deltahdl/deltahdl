#include <algorithm>
#include <cstddef>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
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

}  // namespace

bool VpiIsNetDriverOrLoad(VpiHandle child, VpiHandle net, bool want_driver) {
  if (child->type == vpiPrimTerm) {
    return child->direction == kVpiInout ||
           child->direction == (want_driver ? kVpiOutput : kVpiInput);
  }
  // A force and a continuous assignment drive what their target writes and
  // load what their expression reads, the one without the other unless the
  // net stands on both sides.
  if (child->type == vpiForce || child->type == vpiContAssign) {
    return want_driver ? VpiAssignTargetWrites(child->lhs, *net)
                       : VpiExpressionReads(child->rhs, *net);
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
// driven by nets alone, or by nothing: a net, a bit or a select of one, or a
// concatenation of such, each of whose nets drives its own bits. A variable, a
// constant or any other operation drives the port as something else.
bool DrivenByNets(VpiHandle conn) {
  if (conn == nullptr || VpiIsNetsType(conn->type)) return true;
  if (conn->type == vpiOperation) {
    return VpiIsConcatenationExpression(conn) &&
           std::ranges::all_of(VpiOperationOperands(conn), DrivenByNets);
  }
  return conn->parent != nullptr && VpiIsNetsType(conn->parent->type) &&
         VpiIsVariableSelectType(conn->type);
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
  if (net != nullptr && std::ranges::find(out, net) == out.end()) {
    out.push_back(net);
  }
}

}  // namespace

std::vector<VpiHandle> VpiNetsJoinedThroughPorts(VpiHandle net) {
  // §37.16 details 4 and 16: a port nets drive at both ends passes the drivers
  // and loads of the nets on either end to the other, so the nets it connects
  // share them, however many instances apart.
  std::vector<VpiHandle> joined{net};
  for (std::size_t k = 0; k < joined.size(); ++k) {
    std::vector<VpiHandle> far;
    for (VpiHandle port : VpiNetPortInsts(joined[k])) {
      if (port->low_conn != nullptr && DrivenByNets(port->high_conn) &&
          DrivenByNets(port->low_conn)) {
        NetsNamedIn(port->low_conn, far);
      }
    }
    for (VpiHandle port : VpiNetPorts(joined[k])) {
      if (DrivenByNets(port->high_conn)) NetsNamedIn(port->high_conn, far);
    }
    for (VpiHandle other : far) {
      if (std::ranges::find(joined, other) == joined.end()) {
        joined.push_back(other);
      }
    }
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
