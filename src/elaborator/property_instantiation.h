#pragma once

#include <cstdint>

namespace delta {

// §16.12.1: an instance of a named property may stand as either a
// property_expr or a property_spec. These are the two valid placement
// positions.
enum class PropertyInstancePlacement : uint8_t {
  kAsPropertyExpr,
  kAsPropertySpec,
};

// §16.12.1: the instance is legal at a given placement if and only if the
// body of the named property — substituted with actuals in place of formals —
// is itself a legal property_expr (respectively property_spec) when used in
// place of the instance.
bool IsPropertyInstanceLegal(PropertyInstancePlacement placement,
                             bool body_substitutable_at_placement);

// §16.12.1: if an instance of a named property is used as a property_expr
// operand of any property-building operator, then the named property may
// not have a disable iff clause. This is the only extra constraint that
// §16.12.1 adds to §16.12's general rules.
bool IsPropertyInstanceLegalAsBuildingOperatorOperand(
    bool named_property_has_disable_iff);

}  // namespace delta
