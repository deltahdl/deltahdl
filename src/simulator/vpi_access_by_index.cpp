#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIndexesItsVarBits(const VpiObject& obj) {
  return (obj.type == vpiStructVar || obj.type == vpiUnionVar) &&
         obj.decl_vector;
}

VpiObject* VpiVarBitAt(const VpiObject& obj, int index) {
  for (VpiObject* child : obj.children) {
    if (child->type == vpiVarBit && child->index == index) return child;
  }
  return nullptr;
}

bool VpiHasAccessByIndex(int type) {
  switch (type) {
    case kVpiPort:
    case kVpiReg:
    case vpiBitVar:
    case vpiMemory:
    case vpiRegArray:
    case vpiPackedArrayVar:
    case vpiGenScopeArray:
    case vpiModuleArray:
    case vpiInterfaceArray:
    case vpiProgramArray:
    case vpiGateArray:
    case vpiSwitchArray:
    case vpiUdpArray:
    case vpiNamedEventArray:
      return true;
    default:
      return VpiIsNetsType(type);
  }
}

int VpiGenScopeArraySize(VpiHandle gen_scope_array) {
  if (!gen_scope_array) return 0;
  int count = 0;
  for (auto* child : gen_scope_array->children) {
    if (child->type == vpiGenScope) ++count;
  }
  return count;
}

}  // namespace delta
