#pragma once

#include <cstdint>
#include <string_view>

#include "common/source_loc.h"
#include "lexer/token.h"

namespace delta {

class Arena;
class DiagEngine;
struct Expr;

// Parse the numeric value of an integer literal token's text, ignoring the
// optional size/base prefix and underscore separators. Shared between the
// literal parsing in expr_parser.cpp and the assignment-pattern parsing in
// expr_parser_patterns.cpp; defined once in expr_parser.cpp.
uint64_t ParseIntText(std::string_view text);

// Builds a width/type cast whose target type is carried by an AST node
// (cast->rhs) and whose value is carried by cast->lhs. The cast inherits the
// type node's start location. Pure node construction; the caller has already
// parsed both operands. Shared between the cast parsing in expr_parser.cpp and
// the sized integer literal followed by '(expr) in expr_parser_literals.cpp;
// defined once in expr_parser.cpp.
Expr* MakeNodeCast(Arena& arena, Expr* type_node, Expr* value);

// Builds a bare identifier node carrying the given name text and location.
// Pure node construction; defined in expr_parser.cpp, and shared with the
// loop generate header in parser_generate.cpp, whose genvar_initialization
// names its genvar by an identifier alone.
Expr* MakeIdentifierNode(Arena& arena, std::string_view text, SourceLoc loc);

// Builds a cast whose target type is carried by a name string (cast->text)
// and whose value is carried by cast->lhs, starting at the given location.
// Pure node construction; defined in expr_parser.cpp, and shared with the
// A.6.9 void cast statement in parser_stmt.cpp.
Expr* MakeTextCast(Arena& arena, std::string_view type_text, SourceLoc start,
                   Expr* value);

// Whether `arg` is a class_new or a dynamic_array_new (A.2.4) that
// ParsePrimaryExpr read where an expression starts: a `new` with no class
// scope, which stands only on the right-hand side of a blocking assignment
// (A.6.2). Defined in expr_parser_aux.cpp, and shared with the statement
// parser in parser_stmt.cpp, which takes no such `new` as a statement.
bool IsNewExpr(const Expr* arg);

// Whether `e` is an A.9.3 hierarchical_identifier: identifiers joined by `.`,
// any but the last carrying bit-selects, with no class or package scope.
// `trailing_select` admits bit-selects after the last identifier too, the
// nonrange_select A.6.5 writes after an event trigger's name. Defined in
// parser_clocking.cpp beside the wait_order operand it was written for, and
// shared with the disable statement and the event triggers in parser_stmt.cpp.
bool IsHierarchicalName(const Expr* e, bool trailing_select);

// Builds a postfix increment/decrement node wrapping an already-parsed operand,
// using the already-consumed operator's kind. Pure node construction; defined
// in expr_parser.cpp after the primaries that use it, ParseThisOrSuperExpr and
// ParseIdentifierExpr, which is why it is declared here rather than in the
// file's anonymous namespace.
Expr* MakePostfixUnary(Arena& arena, TokenKind op, Expr* operand);

// Reports `e`, the primary Parser::ParsePrimaryExpr read after a `##` with no
// parenthesis behind it, unless it is one of the two forms A.6.11's
// cycle_delay admits there: an integral number or an identifier. Defined in
// parser_stmt_timing.cpp beside the cycle delay statement, and shared with the
// synchronous drive's cycle delay in parser_stmt.cpp.
void CheckUnparenthesizedCycleDelay(const Expr* e, DiagEngine& diag);

}  // namespace delta
