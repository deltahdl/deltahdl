#include "simulator/vpi_handle_instance.h"

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool TryResolveInstanceRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiInstance) {
    out = VpiInstanceOf(ref);
  } else if (type == kVpiModule) {
    out = VpiModuleOf(ref);
  } else if (type == vpiInstanceArray || type == vpiModuleArray ||
             type == vpiPrimitiveArray) {
    // §37.5 and §37.11: an element reaches the array it belongs to.
    out = VpiInstanceArrayOf(ref, type);
  } else {
    return false;
  }
  return true;
}

}  // namespace delta
