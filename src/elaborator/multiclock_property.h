#ifndef DELTA_ELABORATOR_MULTICLOCK_PROPERTY_H
#define DELTA_ELABORATOR_MULTICLOCK_PROPERTY_H

#include <string>
#include <string_view>
#include <vector>

namespace delta {

bool IsMulticlockedProperty(std::string_view property_clock,
                            const std::vector<std::string>& subproperty_clocks,
                            bool any_subproperty_is_multiclocked_sequence);

}  // namespace delta

#endif
