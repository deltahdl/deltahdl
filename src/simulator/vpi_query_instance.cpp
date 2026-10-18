#include "simulator/vpi_query_instance.h"

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_instance_facts.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiGetInstanceProperty(int property, VpiHandle obj, int& value) {
  // §37.10: a package is the compilation unit's own scope where the unit
  // declares into it, the one whose objects detail 5 names "$unit::name".
  if (property == vpiUnit && obj->type == vpiPackage) {
    value = static_cast<int>(obj->in_compilation_unit);
    return true;
  }
  if (!VpiIsInstanceType(obj->type)) return false;
  const VpiInstanceFacts& facts = obj->instance_facts;
  switch (property) {
    case vpiCellInstance:
      value = static_cast<int>(facts.cell);
      return true;
    case vpiProtected:
      value = static_cast<int>(facts.protected_definition);
      return true;
    case vpiDefNetType:
      value = facts.default_net_type;
      return true;
    case vpiUnconnDrive:
      value = facts.unconnected_drive;
      return true;
    case vpiDefDelayMode:
      value = facts.delay_mode;
      return true;
    case vpiTop:
      value = static_cast<int>(obj->top_module);
      return true;
    default:
      return false;
  }
}

}  // namespace delta
