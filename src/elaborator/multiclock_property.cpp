#include "elaborator/multiclock_property.h"

#include <string>
#include <string_view>
#include <vector>

namespace delta {

bool IsMulticlockedProperty(std::string_view property_clock,
                            const std::vector<std::string>& subproperty_clocks,
                            bool any_subproperty_is_multiclocked_sequence) {
  if (any_subproperty_is_multiclocked_sequence) return true;
  for (const std::string& clock : subproperty_clocks) {
    if (clock != property_clock) return true;
  }
  return false;
}

}  // namespace delta
