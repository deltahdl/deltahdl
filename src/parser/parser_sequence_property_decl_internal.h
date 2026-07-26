#pragma once

#include "parser/ast.h"

namespace delta {

bool IsBuiltinTypeKwForLocalVar(TokenKind k);
bool IsDisallowedLocalVarTypeKw(TokenKind k);
bool LexerCheck(Lexer& lexer, TokenKind kind);

}  // namespace delta
