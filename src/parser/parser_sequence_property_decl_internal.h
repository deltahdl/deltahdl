#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_module.h"

namespace delta {

bool IsBuiltinTypeKwForLocalVar(TokenKind k);

// §16.10 Syntax 16-13 with §6.18: whether the lexer stands at an
// assertion_variable_declaration, its var_data_type a type keyword a local
// may be declared with or a name among `known_types` that a variable's name
// or a packed dimension follows; a type name opening a cast, `nib_t'(a)`,
// starts no declaration. The lexer is left where it stood.
bool AtAssertionVariableDecl(
    Lexer& lexer, const std::unordered_set<std::string_view>& known_types);
bool IsDisallowedLocalVarTypeKw(TokenKind k);
bool LexerCheck(Lexer& lexer, TokenKind kind);

// §16.8 with §16.6: reports a sequence's or a property's formal whose type
// keyword, `type_tok`, is chandle, a type no assertion expression may
// reference; reports nothing for any other keyword.
void ReportChandleFormal(DiagEngine& diag, const Token& type_tok);

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

// §16.14.7: consumes the system function opening a formal's default value in
// a sequence's or a property's port list, records an inferred clocking or
// disable function on the formal just harvested, and reports one placed
// where §16.14.7 forbids it; `clock_default_allowed` says whether the formal's
// type, written or carried, is untyped or `event`.
void ScanSystemDefaultValue(Lexer& lexer, DiagEngine& diag, ModuleItem* item,
                            bool clock_default_allowed);

}  // namespace delta
