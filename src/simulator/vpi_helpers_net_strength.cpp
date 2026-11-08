#include "common/types.h"
#include "simulator/net.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

int VpiChargeStrengthConstant(Strength charge) {
  switch (charge) {
    case Strength::kSmall:
      return vpiSmallCharge;
    case Strength::kLarge:
      return vpiLargeCharge;
    default:
      return vpiMediumCharge;
  }
}

}  // namespace

bool VpiGetNetStrengthProperty(int property, VpiHandle obj, int& out) {
  if (property != vpiChargeStrength) return false;
  const bool kTrireg = VpiIsNetsType(obj->type) && obj->net != nullptr &&
                       obj->net->type == NetType::kTrireg;
  out = kTrireg ? VpiChargeStrengthConstant(obj->net->base_charge_strength) : 0;
  return true;
}

}  // namespace delta
