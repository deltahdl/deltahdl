#pragma once

#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

DataType TypeSpelledBy(const Expr* written);

std::vector<DataType> SpecializationArguments(const Expr& name);

}  // namespace delta
