#include "simulator/vpi_io_decl_stand_in.h"

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiHandle VpiIoDeclStandIn(VpiHandle obj, int relation) {
  if (obj == nullptr || obj->type != vpiIODecl) return obj;
  switch (relation) {
    case vpiSize:
    case vpiSigned:
    case vpiScalar:
    case vpiVector:
    case vpiLeftRange:
    case vpiRightRange:
    case vpiRange:
    case vpiTypespec:
      break;
    default:
      return obj;
  }
  VpiHandle declared = obj->io_expr;
  if (declared != nullptr && declared->type == vpiRefObj) {
    declared = declared->actual;
  }
  return declared != nullptr ? declared : obj;
}

}  // namespace delta
