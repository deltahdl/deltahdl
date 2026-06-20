#ifndef DELTA_ELABORATOR_MULTICLOCK_PROPERTY_H
#define DELTA_ELABORATOR_MULTICLOCK_PROPERTY_H

#include <string>
#include <string_view>
#include <vector>

namespace delta {

// Classifies a property as singly clocked or multiclocked, per IEEE 1800-2023
// §16.13.2.
//
// A clock may be explicitly specified with any property; that clock is the
// property clock. The property is multiclocked when at least one of its
// subproperties is governed by a clock different from the property clock, or at
// least one subproperty is itself a multiclocked sequence. A multiclocked
// sequence used as a subproperty makes the whole property multiclocked even
// when every explicit clock matches the property clock.
//
// `subproperty_clocks` lists the governing clock of each subproperty in source
// order; `any_subproperty_is_multiclocked_sequence` is set when some
// subproperty is a multiclocked sequence (whose legality is established in
// §16.13.1).
bool IsMulticlockedProperty(std::string_view property_clock,
                            const std::vector<std::string>& subproperty_clocks,
                            bool any_subproperty_is_multiclocked_sequence);

}  // namespace delta

#endif  // DELTA_ELABORATOR_MULTICLOCK_PROPERTY_H
