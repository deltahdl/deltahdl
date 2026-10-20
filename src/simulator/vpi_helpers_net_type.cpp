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
      // NetType::kNone, the one value left: no net type.
      return vpiNone;
  }
}

int VpiNetTypeOf(VpiHandle obj) {
  // §37.16 detail 12: an interconnect net or array is of net type
  // vpiInterconnect, one a port declares with no net of the run's behind it,
  // and one whose net in the run a port connection merged into another type.
  if (VpiIsInterconnectSubelementType(obj->type)) return vpiInterconnect;
  if (obj->net == nullptr) return 0;
  // §37.16 detail 11: a net declared with a user-defined nettype (§6.6.7) is a
  // nettype net, and any part of one -- an object whose parent stands for the
  // same net, as a net bit or a select does -- a nettype net select.
  if (obj->net->is_user_nettype) {
    return VpiNetNettypeValue(obj->parent != nullptr &&
                              obj->parent->net == obj->net);
  }
  return VpiNetTypeConstant(obj->net->type);
}

// §23.3.3.7.1: every net a port connects the net `net` to.
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
  // §23.3.3.7.1: the merging is transitive, so the merged net reaches on
  // through every interconnect net among the connections to the first that is
  // not one.
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

// The type the net `net` brings to the net a port connection merges it into:
// for an interconnect net the type the run gave its net, which the elaborator
// merged from the ports its own module connects it to, and for any other net
// its declared type.
static int MergedNetTypeOf(VpiHandle net) {
  if (net->net != nullptr && VpiIsInterconnectSubelementType(net->type)) {
    return VpiNetTypeConstant(net->net->type);
  }
  return VpiNetTypeOf(net);
}

int VpiResolvedNetTypeOf(VpiHandle obj) {
  const int kDeclared = VpiNetTypeOf(obj);
  if (kDeclared != vpiInterconnect) return kDeclared;
  // §23.3.3.7.1: a port connection merges an interconnect net with the net it
  // joins it to, and the merging is transitive, so the merged net reaches on
  // through every interconnect net among them and is of the first other type
  // it reaches.
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
