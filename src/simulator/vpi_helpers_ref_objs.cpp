#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

VpiHandle InstanceHolding(VpiHandle ref_obj) {
  for (VpiHandle holder = ref_obj->parent; holder != nullptr;
       holder = holder->parent) {
    if (VpiIsInstanceType(holder->type)) return holder;
  }
  return nullptr;
}

bool UsesRefObj(VpiHandle expr, VpiHandle ref_obj) {
  for (VpiHandle obj = expr; obj != nullptr && obj->type == vpiRefObj;
       obj = obj->parent) {
    if (obj == ref_obj) return true;
  }
  return false;
}

void CollectInstanceHighConnPorts(VpiHandle instance, VpiHandle ref_obj,
                                  bool subelements,
                                  std::vector<VpiHandle>& out) {
  for (VpiHandle port : instance->children) {
    if (port->type != kVpiPort) continue;
    const bool kConnects = subelements ? UsesRefObj(port->high_conn, ref_obj)
                                       : port->high_conn == ref_obj;
    if (kConnects) out.push_back(port);
  }
}

void CollectHighConnPorts(VpiHandle scope, VpiHandle ref_obj, bool subelements,
                          std::vector<VpiHandle>& out) {
  for (VpiHandle child : scope->children) {
    if (child->type == vpiGenScope || child->type == vpiGenScopeArray) {
      CollectHighConnPorts(child, ref_obj, subelements, out);
    } else if (VpiIsInstanceType(child->type)) {
      CollectInstanceHighConnPorts(child, ref_obj, subelements, out);
    }
  }
}

bool ActualIsInterfaceOrModport(int actual_type) {
  return actual_type == vpiInterface || actual_type == vpiInterfaceArray ||
         actual_type == vpiModport;
}

bool ActualHasTypespec(int actual_type) {
  return VpiIsNetsType(actual_type) || VpiIsVariablesType(actual_type) ||
         actual_type == vpiPartSelect;
}

}  // namespace

int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface) {
  if (!refers_to_interface) return vpiUndefined;
  return is_generic_interface ? 1 : 0;
}

const char* VpiRefObjDefName(VpiHandle ref_obj) {
  VpiHandle actual = ref_obj->actual;
  if (!actual || !ActualIsInterfaceOrModport(actual->type)) return nullptr;
  if (actual->type == vpiModport || actual->def_name.empty()) {
    return actual->name.data();
  }
  return actual->def_name.c_str();
}

VpiHandle VpiRefObjTypespec(VpiHandle ref_obj) {
  VpiHandle actual = ref_obj->actual;
  if (!actual || !ActualHasTypespec(actual->type)) return nullptr;
  for (auto* child : actual->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiRefObjParent(VpiHandle ref_obj) {
  VpiHandle holder = ref_obj->parent;
  return holder != nullptr && holder->type == vpiRefObj ? holder : nullptr;
}

bool VpiIsRefObjPortRelation(int type) {
  return type == vpiLowConn || type == vpiHighConn || type == vpiPortInst;
}

std::vector<VpiHandle> VpiRefObjPorts(int type, VpiHandle ref_obj) {
  std::vector<VpiHandle> ports;
  VpiHandle instance = InstanceHolding(ref_obj);
  if (instance == nullptr) return ports;
  if (type != vpiLowConn) {
    CollectHighConnPorts(instance, ref_obj, type == vpiPortInst, ports);
    return ports;
  }
  for (VpiHandle port : instance->children) {
    if (port->type == kVpiPort && port->low_conn == ref_obj) {
      ports.push_back(port);
    }
  }
  return ports;
}

}  // namespace delta
