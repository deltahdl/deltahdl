#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct StructFieldInfo;
struct StructTypeInfo;

Logic4Vec ExtractStructField(const Logic4Vec& value, const StructTypeInfo* info,
                             std::string_view field, Arena& arena);

const StructFieldInfo* StructMemberOfClassType(const StructTypeInfo* info,
                                               std::string_view path,
                                               SimContext& ctx,
                                               uint32_t* bit_offset);

std::optional<Logic4Vec> StructMemberObjectRead(const Logic4Vec& value,
                                                const StructTypeInfo* info,
                                                std::string_view field,
                                                SimContext& ctx, Arena& arena);

bool TryImplicitThisHandleMember(std::string_view base_name,
                                 std::string_view field_name, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta
