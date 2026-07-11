#include "elaborator/property_instantiation.h"

namespace delta {

bool IsPropertyInstanceLegal(PropertyInstancePlacement /*placement*/,
                             bool body_substitutable_at_placement) {
  // §16.12.1: legality reduces to substitutability at the placement site —
  // the placement chooses which yardstick (property_expr vs property_spec)
  // applies, but the predicate is the same.
  return body_substitutable_at_placement;
}

}  // namespace delta
