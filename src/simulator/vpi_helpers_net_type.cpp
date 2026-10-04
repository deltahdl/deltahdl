#include "common/types.h"
#include "simulator/net.h"
#include "simulator/vpi_constants.h"
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
    case NetType::kNone:
      return vpiNone;
    case NetType::kInterconnect:
      return vpiInterconnect;
  }
  return 0;
}

}  // namespace

int VpiNetTypeOf(VpiHandle obj) {
  if (obj->net == nullptr) return 0;
  // A net declared with a user-defined nettype (§6.6.7) is a nettype net.
  if (obj->net->is_user_nettype) return vpiNettypeNet;
  return NetTypeConstant(obj->net->type);
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
