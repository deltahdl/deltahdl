#include "elaborator/cross_automatic_types.h"

namespace delta {

CrossValTypeDef BuildCrossValType(const std::vector<CrossValMember>& coverpoints) {
  // §19.6.1.3: one struct member for each coverpoint in the cross, carrying that
  // coverpoint's name and type, in order.
  CrossValTypeDef def;
  def.members = coverpoints;
  return def;
}

CrossQueueTypeDef BuildCrossQueueType() {
  // §19.6.1.3: an unbounded queue of CrossValType elements.
  return CrossQueueTypeDef{};
}

std::string CrossValMemberDefaultBoundType(int64_t expr_bit_width) {
  // §19.6.1.3: bounds default to [$bits(coverpoint_expression)-1:0] when not
  // otherwise evident. A coverpoint expression always occupies at least one bit.
  int64_t high = expr_bit_width >= 1 ? expr_bit_width - 1 : 0;
  return "logic [" + std::to_string(high) + ":0]";
}

bool CrossAutoTypeIsVisible(std::string_view querying_scope,
                            std::string_view defining_cross_scope) {
  // §19.6.1.3: the type names are visible only within the defining cross.
  return querying_scope == defining_cross_scope;
}

bool IsImplicitCrossTypedefName(std::string_view name) {
  // §19.6.1.3: CrossValType and CrossQueueType behave as implicit typedefs in
  // the cross body even though explicit typedefs are not allowed there.
  return name == kCrossValTypeName || name == kCrossQueueTypeName;
}

}  // namespace delta
