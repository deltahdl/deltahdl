#include "common/types.h"
#include "simulator/net.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The Annex K constant of a trireg net's charge strength, which §6.6.4.2 makes
// small, medium or large.
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
  // §37.16 (figure): a trireg net's charge strength, the one it was declared
  // with; a net of any other type holds no charge and reports none.
  const bool kTrireg = VpiIsNetsType(obj->type) && obj->net != nullptr &&
                       obj->net->type == NetType::kTrireg;
  out = kTrireg ? VpiChargeStrengthConstant(obj->net->base_charge_strength) : 0;
  return true;
}

}  // namespace delta
