#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct ClassObject;
struct ClassTypeInfo;
struct Expr;
struct StructTypeInfo;

Logic4Vec ResolveClassFieldChain(ClassObject* obj,
                                 const ClassTypeInfo* declared_type,
                                 std::string_view field_path, SimContext& ctx,
                                 Arena& arena);

uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx);

std::string CastTypeKey(const Expr* expr, SimContext& ctx);

size_t MemberPathSplit(const std::string& path, SimContext& ctx);

const StructTypeInfo* StructLayoutOfName(std::string_view name,
                                         SimContext& ctx);

std::string TagKeyOfName(std::string_view name, SimContext& ctx);

const StructTypeInfo* PropertyAggregateLayout(std::string_view name,
                                              SimContext& ctx,
                                              std::string& key);

std::string StripRootPrefix(const std::string& name);

}  // namespace delta
