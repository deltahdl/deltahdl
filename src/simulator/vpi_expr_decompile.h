#pragma once

#include <string>

#include "parser/ast_expr.h"

namespace delta {

// §37.59 detail 2: the vpiDecompile of `expr`, an expression functionally
// equivalent to the one the source wrote, each operand and operator one space
// apart and parenthesized only where §11.3.2's precedence would otherwise
// regroup it. Empty for an expression holding a kind this cannot render, which
// then reports no decompiled form rather than a wrong one.
std::string VpiExprDecompile(const Expr* expr);

}  // namespace delta
