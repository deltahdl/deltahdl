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

uint64_t ParseIntText(std::string_view text);

Expr* MakeNodeCast(Arena& arena, Expr* type_node, Expr* value);

Expr* MakeIdentifierNode(Arena& arena, std::string_view text, SourceLoc loc);

Expr* MakeTextCast(Arena& arena, std::string_view type_text, SourceLoc start,
                   Expr* value);

bool IsNewExpr(const Expr* arg);

bool IsHierarchicalName(const Expr* e, bool trailing_select);

Expr* MakePostfixUnary(Arena& arena, TokenKind op, Expr* operand);

void CheckUnparenthesizedCycleDelay(const Expr* e, DiagEngine& diag);

bool IsPsIdentifier(const Expr* e);

bool WithOpensRange(Lexer& lexer);

void ReportPredicateOperator(const Expr* e, DiagEngine& diag);

bool ReportUnaryOperatorAfterOperand(const Token& tok, DiagEngine& diag);

bool EndsExpression(const Token& tok);

void ReportEmptyConcatItems(const Expr* concat, DiagEngine& diag);

bool IsNamedLvalue(const Expr* e);

bool HasLvalueForm(const Expr* e);

void ReportLocalQualifier(SourceLoc loc, DiagEngine& diag);

void CheckIncDecOperand(const Expr* operand, DiagEngine& diag);

}  // namespace delta
