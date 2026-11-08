#pragma once

#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct ClassTypeInfo;
struct DataType;

std::string_view DeclaredClassKey(const DataType& type, SimContext& ctx,
                                  Arena& arena);

std::string_view DeclaredClassKeyInScope(const DataType& type,
                                         const ClassTypeInfo* declaring,
                                         SimContext& ctx, Arena& arena);

const DataType* TypeOfThisNamed(const DataType* type, const ClassTypeInfo* cls,
                                SimContext& ctx);

}  // namespace delta
