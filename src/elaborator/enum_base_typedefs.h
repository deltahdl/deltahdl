#pragma once

#include <vector>

#include "parser/ast_type.h"

namespace delta {

class Arena;
struct CompilationUnit;

DataType EnumBaseAsWritten(const DataType& type);

void ResolveEnumBaseTypedefs(const std::vector<CompilationUnit*>& units,
                             Arena& arena);

}  // namespace delta
