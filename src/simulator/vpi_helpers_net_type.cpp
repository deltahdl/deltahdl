#include <algorithm>
#include <cstddef>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

int VpiNetTypeConstant(NetType type) {
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
      return vpiNone;
  }
}

int VpiNetTypeOf(VpiHandle obj) {
  if (VpiIsInterconnectSubelementType(obj->type)) return vpiInterconnect;
  if (obj->net == nullptr) return 0;
  if (obj->net->is_user_nettype) {
    return VpiNetNettypeValue(obj->parent != nullptr &&
                              obj->parent->net == obj->net);
  }
  return VpiNetTypeConstant(obj->net->type);
}

static std::vector<VpiHandle> VpiConnectedNets(VpiHandle net) {
  std::vector<VpiHandle> connected;
  for (VpiObject* child : net->parent->children) {
    if (child->type == kVpiPort && child->low_conn == net &&
        child->high_conn != nullptr) {
      connected.push_back(child->high_conn);
    }
    if (!VpiIsInstanceType(child->type)) continue;
    for (VpiObject* port : child->children) {
      if (port->type == kVpiPort && port->high_conn == net &&
          port->low_conn != nullptr) {
        connected.push_back(port->low_conn);
      }
    }
  }
  return connected;
}

VpiHandle VpiMergedTypedNet(VpiHandle net) {
  std::vector<VpiHandle> merged = {net};
  for (std::size_t i = 0; i < merged.size(); ++i) {
    for (VpiHandle next : VpiConnectedNets(merged[i])) {
      if (!VpiIsInterconnectSubelementType(next->type)) return next;
      if (std::ranges::find(merged, next) == merged.end()) {
        merged.push_back(next);
      }
    }
  }
  return nullptr;
}

static int MergedNetTypeOf(VpiHandle net) {
  if (net->net != nullptr && VpiIsInterconnectSubelementType(net->type)) {
    return VpiNetTypeConstant(net->net->type);
  }
  return VpiNetTypeOf(net);
}

int VpiResolvedNetTypeOf(VpiHandle obj) {
  const int kDeclared = VpiNetTypeOf(obj);
  if (kDeclared != vpiInterconnect) return kDeclared;
  std::vector<VpiHandle> merged = {obj};
  for (std::size_t i = 0; i < merged.size(); ++i) {
    const int kMerged = MergedNetTypeOf(merged[i]);
    if (kMerged != 0 && kMerged != vpiNone && kMerged != vpiInterconnect) {
      return kMerged;
    }
    if (VpiNetTypeOf(merged[i]) != vpiInterconnect) continue;
    for (VpiHandle next : VpiConnectedNets(merged[i])) {
      if (std::ranges::find(merged, next) == merged.end()) {
        merged.push_back(next);
      }
    }
  }
  return kDeclared;
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
