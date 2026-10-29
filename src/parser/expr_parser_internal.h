#pragma once

#include <cstdint>
#include <string_view>

#include "common/source_loc.h"
#include "lexer/token.h"

namespace delta {

class Arena;
class DiagEngine;
class Lexer;
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

// Whether `e`, a primary Parser::ParsePrimaryExpr read, is an A.9.3
// ps_identifier: an identifier alone, or under one package scope or `$unit`'s.
// A class scope reads the same and is admitted with it. Defined in
// parser_stmt_timing.cpp beside the cycle delay's identifier test it widens,
// and shared with a randsequence rule's weight in parser_randsequence.cpp.
bool IsPsIdentifier(const Expr* e);

// Whether the lexer stands at a `with` that opens a bracketed range, A.8.1's
// `with [ array_range_expression ]`, rather than A.8.2's parenthesized
// expression or constraint block. Defined in expr_parser_calls.cpp beside the
// with clause, and shared with the stream_expression in expr_parser_aux.cpp,
// Parser::ParseExpr in expr_parser.cpp and the expression statement in
// parser_stmt.cpp.
bool WithOpensRange(Lexer& lexer);

// Reports `e` when its top is a `matches` or `&&&`, which A.6.6 confines to
// the predicate of an if statement or a conditional operator. Defined in
// expr_parser_calls.cpp, and shared by Parser::ParseExpr with the
// stream_expression, which reads its operand short of ParseExpr.
void ReportPredicateOperator(const Expr* e, DiagEngine& diag);

// §5.5: a unary operator stands to the left of its operand. Reports `tok`
// where it is one of the operators A.8.6 makes unary only (!, ~, ~& and ~|),
// met where an operand has just ended, and says whether it did. Defined in
// expr_parser_aux.cpp, and called by Parser::ParseInfixBp.
bool ReportUnaryOperatorAfterOperand(const Token& tok, DiagEngine& diag);

// Whether `tok` closes the expression before it rather than beginning an
// operand: a separator or closing bracket, or the end of the text. Defined in
// expr_parser_aux.cpp.
bool EndsExpression(const Token& tok);

// Reports each item of `concat`, a concatenation, a multiple concatenation or
// a streaming concatenation, that is `{}`: A.8.1's footnote 40 makes that the
// empty unpacked array concatenation of §10.10 alone. Defined in
// expr_parser_calls.cpp beside Parser::ParseConcatenation, and shared with
// the stream in expr_parser_aux.cpp.
void ReportEmptyConcatItems(const Expr* concat, DiagEngine& diag);

// A.8.5's (printed page 1212) name form of an lvalue: a name, scoped or
// reached through member selects, under any selects, rooted at the identifier
// the parser heads a name with, that of `this`, `super`, a `$root.` name and a
// `$unit::` name included. A select or member of a concatenation, a call's
// result, a cast or anything written in parentheses is rooted at no name.
// Defined in expr_parser_aux.cpp, and shared with the statement parser in
// parser_stmt.cpp, where a `new` is assigned to one alone, and with
// IsNetLvalue in parser_toplevel.cpp.
bool IsNamedLvalue(const Expr* e);

// Whether `e` has a form A.8.5 (printed page 1212) gives variable_lvalue,
// which covers every form it gives net_lvalue: a name under selects, a
// concatenation of such targets, an assignment pattern of them, typed or not,
// or a streaming concatenation. None is written in parentheses. A replication
// is left to §11.4.12.1's report on a target holding one, and a select within
// a concatenation to §11.4.12's. Defined in expr_parser_aux.cpp, and shared by
// the procedural assignment targets in parser_stmt.cpp with the operand of an
// increment or decrement and the target of an assignment within an expression.
bool HasLvalueForm(const Expr* e);

// Reports the `local::` qualifier at `loc` as standing outside an inline
// constraint block, the one place A.10 footnote 48 admits it. Defined in
// expr_parser.cpp beside Parser::ParseLocalScopeExpr, and shared with the
// token check of a class's own constraint block in parser_constraint_items.cpp.
void ReportLocalQualifier(SourceLoc loc, DiagEngine& diag);

// Reports `operand`, the operand of a prefix or a postfix `++` or `--`, unless
// it has the form of A.8.3's variable_lvalue. Defined in expr_parser_aux.cpp,
// and shared by Parser::ParsePrefixExpr in expr_parser.cpp with the postfix
// form Parser::ParseNameTail reads in expr_parser_calls.cpp.
void CheckIncDecOperand(const Expr* operand, DiagEngine& diag);

}  // namespace delta
