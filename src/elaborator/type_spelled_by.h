#pragma once

#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

DataType TypeSpelledBy(const Expr* written);

}  // namespace delta
