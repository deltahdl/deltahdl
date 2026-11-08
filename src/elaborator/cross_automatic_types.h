#ifndef DELTA_ELABORATOR_CROSS_AUTOMATIC_TYPES_H
#define DELTA_ELABORATOR_CROSS_AUTOMATIC_TYPES_H

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

inline constexpr std::string_view kCrossValTypeName = "CrossValType";
inline constexpr std::string_view kCrossQueueTypeName = "CrossQueueType";

struct CrossValMember {
  std::string name;
  std::string type;
};

struct CrossValTypeDef {
  std::vector<CrossValMember> members;
};

struct CrossQueueTypeDef {
  std::string_view element_type = kCrossValTypeName;
  bool unbounded = true;
};

CrossValTypeDef BuildCrossValType(
    const std::vector<CrossValMember>& coverpoints);

CrossQueueTypeDef BuildCrossQueueType();

std::string CrossValMemberDefaultBoundType(int64_t expr_bit_width);

bool CrossAutoTypeIsVisible(std::string_view querying_scope,
                            std::string_view defining_cross_scope);

bool IsImplicitCrossTypedefName(std::string_view name);

}  // namespace delta

#endif
