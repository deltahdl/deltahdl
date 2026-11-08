#pragma once

#include "lexer/lexer.h"
#include "parser/ast_design.h"

namespace delta {

void BindFsmPragmas(const Lexer& lexer, CompilationUnit& unit);

}  // namespace delta
