#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// §37.15 Reference objects: what a ref obj answers of its own. They sit in a
// file of their own because vpi_helpers_nets.cpp, which holds §37.14, had grown
// to the length .github/workflows/deltahdl.yml admits a source file.

namespace delta {

namespace {

// The instance a ref obj stands in: the nearest of its holders that is one,
// past the io decl or the ref obj holding it.
VpiHandle InstanceHolding(VpiHandle ref_obj) {
  for (VpiHandle holder = ref_obj->parent; holder != nullptr;
       holder = holder->parent) {
    if (VpiIsInstanceType(holder->type)) return holder;
  }
  return nullptr;
}

// Whether `expr` is `ref_obj` or a ref obj that is a subelement of it, as
// s.initiator is of s (detail 4).
bool UsesRefObj(VpiHandle expr, VpiHandle ref_obj) {
  for (VpiHandle obj = expr; obj != nullptr && obj->type == vpiRefObj;
       obj = obj->parent) {
    if (obj == ref_obj) return true;
  }
  return false;
}

// The ports of `instance` whose higher connection is `ref_obj` itself or,
// where `subelements` is set, a use of it.
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

// The same of the instances `scope` holds, reaching into the generate blocks
// it holds.
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

// §37.15 detail 6: the actual kinds whose definition/modport name a ref obj's
// vpiDefName reports - an interface, an interface array, or a modport.
bool ActualIsInterfaceOrModport(int actual_type) {
  return actual_type == vpiInterface || actual_type == vpiInterfaceArray ||
         actual_type == vpiModport;
}

// §37.15 detail 7: the actual kinds that carry a typespec - a net, a variable,
// or a part select, of any of the kinds §37.16 and §37.17 group under the nets
// and variables classes.
bool ActualHasTypespec(int actual_type) {
  return VpiIsNetsType(actual_type) || VpiIsVariablesType(actual_type) ||
         actual_type == vpiPartSelect;
}

}  // namespace

int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface) {
  // §37.15 detail 5: a ref obj that refers to an interface reports whether that
  // interface is generic; any other ref obj reports vpiUndefined.
  if (!refers_to_interface) return vpiUndefined;
  return is_generic_interface ? 1 : 0;
}

const char* VpiRefObjDefName(VpiHandle ref_obj) {
  // §37.15 detail 6: a modport actual reports its own name, and an interface or
  // interface array actual the definition it is an instance of, which an
  // instance records apart from its own name (§38.11).
  VpiHandle actual = ref_obj->actual;
  if (!actual || !ActualIsInterfaceOrModport(actual->type)) return nullptr;
  if (actual->type == vpiModport || actual->def_name.empty()) {
    return actual->name.data();
  }
  return actual->def_name.c_str();
}

VpiHandle VpiRefObjTypespec(VpiHandle ref_obj) {
  // §37.15 detail 7: NULL unless the ref obj's actual is a net, variable, or
  // part select; in that case the typespec the actual holds, one of the
  // concrete kinds §37.25 fills the typespec class with.
  VpiHandle actual = ref_obj->actual;
  if (!actual || !ActualHasTypespec(actual->type)) return nullptr;
  for (auto* child : actual->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiRefObjParent(VpiHandle ref_obj) {
  // §37.15 (figure) with detail 4: vpiParent reaches only a ref obj, the one a
  // subelement ref obj selects from; the io decl or instance holding any other
  // ref obj is not its parent.
  VpiHandle holder = ref_obj->parent;
  return holder != nullptr && holder->type == vpiRefObj ? holder : nullptr;
}

bool VpiIsRefObjPortRelation(int type) {
  return type == vpiLowConn || type == vpiHighConn || type == vpiPortInst;
}

std::vector<VpiHandle> VpiRefObjPorts(int type, VpiHandle ref_obj) {
  // §37.15 (figure): vpiLowConn reaches the ports of the ref obj's own instance
  // it is the lower connection of, vpiHighConn the ports of the instances
  // within it whose higher connection it is, and vpiPortInst those ports and
  // the ones a subelement of it connects, s.initiator as well as s.
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
