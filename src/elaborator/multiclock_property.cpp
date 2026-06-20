#include "elaborator/multiclock_property.h"

namespace delta {

bool IsMulticlockedProperty(std::string_view property_clock,
                            const std::vector<std::string>& subproperty_clocks,
                            bool any_subproperty_is_multiclocked_sequence) {
  // §16.13.2: a multiclocked sequence subproperty makes the enclosing property
  // multiclocked regardless of the explicit clocks present.
  if (any_subproperty_is_multiclocked_sequence) return true;
  // Otherwise the property is multiclocked exactly when some subproperty is
  // governed by a clock other than the property clock.
  for (const std::string& clock : subproperty_clocks) {
    if (clock != property_clock) return true;
  }
  return false;
}

}  // namespace delta
