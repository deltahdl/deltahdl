#pragma once

#include <cstddef>
#include <cstdint>
#include <string>

namespace delta {

class SimContext;
struct ClassDecl;
struct ClassTypeInfo;
struct DataType;

std::string TypeKey(const DataType& type, SimContext& ctx);

std::string TypeKeySeenFrom(const DataType& type, const ClassTypeInfo* from,
                            uint32_t width, SimContext& ctx);

std::string TypeActualKey(const ClassDecl* decl, size_t i,
                          const DataType* actual, SimContext& ctx);

}  // namespace delta
