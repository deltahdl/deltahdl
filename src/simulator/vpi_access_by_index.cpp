#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiHasAccessByIndex(int type) {
  switch (type) {
    case kVpiModule:         // §38.19: module indexes its ports
    case kVpiPort:           // a port indexes its bits
    case kVpiReg:            // a reg indexes its bits
    case vpiBitVar:          // §37.17: so does a bit variable
    case vpiMemory:          // a memory indexes its words
    case vpiRegArray:        // a reg array indexes its elements
    case vpiPackedArrayVar:  // a packed array indexes its elements
    case vpiGenScopeArray:   // §37.85: a gen scope array indexes its gen scopes
    case vpiModuleArray:     // §37.11: an instance array indexes its elements
    case vpiInterfaceArray:
    case vpiProgramArray:
    case vpiGateArray:
    case vpiSwitchArray:
    case vpiUdpArray:
      return true;
    // §37.16 (figure): the `nets` class draws access by index, so a net of
    // every kind it groups indexes its bits or, an array net, its nets.
    default:
      return VpiIsNetsType(type);
  }
}

int VpiGenScopeArraySize(VpiHandle gen_scope_array) {
  // §37.85 detail 1: the size of a gen scope array is the number of elements in
  // the array, i.e. the gen scope objects it holds. It is counted from the
  // array's gen scope element children rather than read from any stored width.
  if (!gen_scope_array) return 0;
  int count = 0;
  for (auto* child : gen_scope_array->children) {
    if (child->type == vpiGenScope) ++count;
  }
  return count;
}

}  // namespace delta
