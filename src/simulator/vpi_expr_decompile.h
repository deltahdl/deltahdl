#pragma once

#include <string>

#include "parser/ast_expr.h"

namespace delta {

std::string VpiExprDecompile(const Expr* expr);

}  // namespace delta
