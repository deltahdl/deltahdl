#include "common/types.h"
#include "simulator/net.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.16: the Annex K constant for a net declared of `type`.
int NetTypeConstant(NetType type) {
  switch (type) {
    case NetType::kWire:
      return vpiWire;
    case NetType::kTri:
      return vpiTri;
    case NetType::kWand:
      return vpiWand;
    case NetType::kTriand:
      return vpiTriAnd;
    case NetType::kWor:
      return vpiWor;
    case NetType::kTrior:
      return vpiTriOr;
    case NetType::kTri0:
      return vpiTri0;
    case NetType::kTri1:
      return vpiTri1;
    case NetType::kSupply0:
      return vpiSupply0;
    case NetType::kSupply1:
      return vpiSupply1;
    case NetType::kTrireg:
      return vpiTriReg;
    case NetType::kUwire:
      return vpiUwire;
    case NetType::kInterconnect:
      return vpiInterconnect;
    default:
      // NetType::kNone, the one value left: no net type.
      return vpiNone;
  }
}

}  // namespace

int VpiNetTypeOf(VpiHandle obj) {
  if (obj->net == nullptr) return 0;
  // A net declared with a user-defined nettype (§6.6.7) is a nettype net.
  if (obj->net->is_user_nettype) return vpiNettypeNet;
  return NetTypeConstant(obj->net->type);
}

// §23.3.3.7.1: the type of the net a port connects `net` to: for the net a
// port of its instance stands for inside, the net the instantiation connects
// to the port, and for a net of an instance, the net inside an instance it
// holds that a port connects it to; 0 where no port connects it to one.
static int ConnectedNetType(VpiHandle net) {
  for (const VpiObject* child : net->parent->children) {
    if (child->type == kVpiPort && child->low_conn == net &&
        child->high_conn != nullptr) {
      return VpiNetTypeOf(child->high_conn);
    }
    if (!VpiIsInstanceType(child->type)) continue;
    for (const VpiObject* port : child->children) {
      if (port->type == kVpiPort && port->high_conn == net &&
          port->low_conn != nullptr) {
        return VpiNetTypeOf(port->low_conn);
      }
    }
  }
  return 0;
}

int VpiResolvedNetTypeOf(VpiHandle obj) {
  // An interconnect port's net carries no net of its own; it is an
  // interconnect net all the same (§37.24).
  const int kDeclared =
      obj->type == vpiInterconnectNet ? vpiInterconnect : VpiNetTypeOf(obj);
  if (kDeclared != vpiInterconnect) return kDeclared;
  const int kConnected = ConnectedNetType(obj);
  return kConnected != 0 ? kConnected : kDeclared;
}

const char* VpiNetTypeConstantName(int net_type) {
  switch (net_type) {
    case vpiWire:
      return "vpiWire";
    case vpiWand:
      return "vpiWand";
    case vpiWor:
      return "vpiWor";
    case vpiTri:
      return "vpiTri";
    case vpiTri0:
      return "vpiTri0";
    case vpiTri1:
      return "vpiTri1";
    case vpiTriReg:
      return "vpiTriReg";
    case vpiTriAnd:
      return "vpiTriAnd";
    case vpiTriOr:
      return "vpiTriOr";
    case vpiSupply1:
      return "vpiSupply1";
    case vpiSupply0:
      return "vpiSupply0";
    case vpiNone:
      return "vpiNone";
    case vpiUwire:
      return "vpiUwire";
    case vpiNettypeNet:
      return "vpiNettypeNet";
    case vpiNettypeNetSelect:
      return "vpiNettypeNetSelect";
    case vpiInterconnect:
      return "vpiInterconnect";
    default:
      return nullptr;
  }
}

}  // namespace delta
