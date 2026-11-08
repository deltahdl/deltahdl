#include "elaborator/property_instantiation.h"

namespace delta {

bool IsPropertyInstanceLegal(PropertyInstancePlacement,
                             bool body_substitutable_at_placement) {
  return body_substitutable_at_placement;
}

}  // namespace delta
