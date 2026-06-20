#pragma once

// Umbrella header for the parser AST. The declarations are split across topical
// sub-headers, each with its own include guard; this file includes them in
// dependency order so that #include "parser/ast.h" continues to provide the
// full AST as before.
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
