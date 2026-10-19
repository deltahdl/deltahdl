#include <algorithm>

#include "simulator/vpi_constants.h"
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

namespace {

// Whether the expression object `expr` names the net `net`, itself or a bit of
// it, or reads it among its operands at any depth.
bool NamesNet(const VpiObject* expr, const VpiObject* net) {
  if (expr == nullptr) return false;
  if (expr == net || expr->parent == net) return true;
  return expr->type == vpiOperation &&
         std::ranges::any_of(expr->children, [net](const VpiObject* operand) {
           return NamesNet(operand, net);
         });
}

}  // namespace

bool VpiIsNetDriverOrLoad(VpiHandle child, VpiHandle net, bool want_driver) {
  if (child->type == vpiPrimTerm) {
    return child->direction == kVpiInout ||
           child->direction == (want_driver ? kVpiOutput : kVpiInput);
  }
  if (child->type == vpiForce) {
    return NamesNet(want_driver ? child->lhs : child->rhs, net);
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
