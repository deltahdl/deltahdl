#include <algorithm>
#include <cstddef>
#include <ranges>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsPortsType(int type) { return type == vpiPort || type == vpiPortBit; }

bool VpiIsNetDriverType(int type) {
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
  if (VpiIsPortsType(type)) return true;
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

bool VpiIsConcatenationExpression(const VpiObject* expr) {
  return expr->op_type == vpiConcatOp || expr->op_type == vpiMultiConcatOp;
}

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
  if (!(want_driver ? VpiIsNetDriverType(child->type)
                    : VpiIsNetLoadType(child->type))) {
    return false;
  }
  if (child->type == vpiPrimTerm) {
    return child->direction == kVpiInout ||
           child->direction == (want_driver ? kVpiOutput : kVpiInput);
  }
  if (child->type == vpiForce || child->type == vpiContAssign) {
    return AssignmentDrivesOrLoads(*child, *net, want_driver);
  }
  if (child->type == vpiDelayTerm && child->parent != nullptr &&
      child->parent->type == vpiDelayDevice) {
    return (child->parent->out_term == child) == want_driver;
  }
  if (VpiIsPortsType(child->type)) {
    return VpiPortIsComplexExpressionLoad(child) != want_driver;
  }
  return true;
}

namespace {

bool DrivenByNets(VpiHandle conn) {
  if (conn == nullptr || VpiIsNetsType(conn->type)) return true;
  if (conn->type == vpiOperation) {
    return VpiIsConcatenationExpression(conn) &&
           std::ranges::all_of(VpiOperationOperands(conn), DrivenByNets);
  }
  return conn->parent != nullptr && VpiIsNetsType(conn->parent->type);
}

bool PassesValues(int direction, bool inward) {
  return direction == vpiInout || direction == (inward ? vpiInput : vpiOutput);
}

VpiHandle ConnectionAt(VpiHandle conn, int place) {
  if (conn == nullptr || conn->type != vpiOperation ||
      conn->op_type != vpiConcatOp) {
    return conn;
  }
  const std::vector<VpiHandle> kOperands = VpiOperationOperands(conn);
  for (VpiHandle operand : std::views::reverse(kOperands)) {
    if (place < operand->size) return ConnectionAt(operand, place);
    place -= operand->size;
  }
  return nullptr;
}

VpiHandle HigherConnectionOf(VpiHandle port) {
  if (port->type != vpiPortBit) return port->high_conn;
  return ConnectionAt(port->parent->high_conn, port->bit_offset);
}

}  // namespace

std::vector<VpiHandle> VpiNetPortDrivers(VpiHandle net) {
  std::vector<VpiHandle> ports;
  for (VpiHandle port : VpiNetPortInsts(net)) {
    if (PassesValues(port->direction, false) && !DrivenByNets(port->low_conn)) {
      ports.push_back(port);
    }
  }
  for (VpiHandle port : VpiNetPorts(net)) {
    if (PassesValues(port->direction, true) &&
        !DrivenByNets(HigherConnectionOf(port))) {
      ports.push_back(port);
    }
  }
  return ports;
}

namespace {

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
  std::vector<VpiHandle> joined{net};
  for (std::size_t k = 0; k < joined.size(); ++k) {
    AddNetsJoinedTo(joined[k], joined);
  }
  return joined;
}

std::vector<VpiHandle> VpiNetLocalPorts(VpiHandle net, bool want_driver) {
  std::vector<VpiHandle> ports;
  for (VpiHandle port : VpiNetPorts(net)) {
    if (PassesValues(port->direction, want_driver)) ports.push_back(port);
  }
  return ports;
}

namespace {

void CollectAroundDelayTerm(VpiHandle term, VpiHandle net, bool want_driver,
                            std::vector<VpiHandle>& found) {
  for (VpiHandle child : net->children) {
    if (child->parent != term->parent &&
        VpiIsNetDriverOrLoad(child, net, want_driver)) {
      found.push_back(child);
    }
  }
}

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

bool BearsOnBit(VpiHandle child, VpiHandle bit) {
  if (child->type == vpiPrimTerm) {
    return VpiExpressionUses(child->children.front(), *bit);
  }
  return child->type == vpiForce || child->type == vpiContAssign;
}

void CollectFromVector(VpiHandle bit, bool want_driver,
                       std::vector<VpiHandle>& found) {
  if (bit->parent == nullptr) return;
  for (VpiHandle child : bit->parent->children) {
    if (BearsOnBit(child, bit) &&
        VpiIsNetDriverOrLoad(child, bit, want_driver)) {
      found.push_back(child);
    }
  }
}

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
      CollectFromVector(joined, want_driver, found);
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
  if (port->direction != vpiInput) return false;
  VpiObject* expr = port->high_conn;
  if (!expr || expr->type != vpiOperation) return false;
  return !VpiIsConcatenationExpression(expr);
}

}  // namespace delta
