#pragma once

#include <string_view>

#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "parser/ast.h"

namespace delta {

bool IsBuiltinTypeKwForLocalVar(TokenKind k);
bool IsDisallowedLocalVarTypeKw(TokenKind k);
bool LexerCheck(Lexer& lexer, TokenKind kind);

// §16.10: whether `name` is a local variable of the sequence or property
// declaration `item`, one its body declares or a local variable formal
// argument of its port list (§16.8.2).
bool IsLocalVariableOfDecl(const ModuleItem* item, std::string_view name);

// §16.10 and Annex F.5.1: consumes the parenthesized event group after a
// clocking event's `@` and reports each identifier in it that names a local
// variable of `item`, since a clock's condition may not depend on one. Leaves
// the lexer after the group's closing parenthesis, or where it stood when no
// group opened.
void ScanClockEventGroupForLocals(Lexer& lexer, DiagEngine& diag,
                                  const ModuleItem* item);

}  // namespace delta
