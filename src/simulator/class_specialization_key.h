#pragma once

#include <cstddef>
#include <string>

namespace delta {

class SimContext;
struct ClassDecl;
struct DataType;

std::string TypeActualKey(const ClassDecl* decl, size_t i,
                          const DataType* actual, SimContext& ctx);

}  // namespace delta
