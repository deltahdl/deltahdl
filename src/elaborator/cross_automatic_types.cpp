#include "elaborator/cross_automatic_types.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

CrossValTypeDef BuildCrossValType(
    const std::vector<CrossValMember>& coverpoints) {
  CrossValTypeDef def;
  def.members = coverpoints;
  return def;
}

CrossQueueTypeDef BuildCrossQueueType() { return CrossQueueTypeDef{}; }

std::string CrossValMemberDefaultBoundType(int64_t expr_bit_width) {
  int64_t high = expr_bit_width >= 1 ? expr_bit_width - 1 : 0;
  return "logic [" + std::to_string(high) + ":0]";
}

bool CrossAutoTypeIsVisible(std::string_view querying_scope,
                            std::string_view defining_cross_scope) {
  return querying_scope == defining_cross_scope;
}

bool IsImplicitCrossTypedefName(std::string_view name) {
  return name == kCrossValTypeName || name == kCrossQueueTypeName;
}

}  // namespace delta
