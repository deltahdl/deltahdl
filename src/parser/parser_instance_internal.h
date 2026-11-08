#pragma once

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

namespace delta {

void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name);

bool IsNetLvalue(const Expr* e);

}  // namespace delta
