#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

using ActualsByFormal = std::unordered_map<std::string_view, Expr*>;

Expr* SubstituteFormals(const Expr* e, const ActualsByFormal& actuals,
                        Arena& arena);

ActualsByFormal BindActuals(const std::vector<std::string_view>& formals,
                            const Expr* instance);

ActualsByFormal BindActualsWithDefaults(
    const std::vector<std::string_view>& formals,
    const std::vector<Expr*>& defaults, const Expr* instance);

Expr* EventAsActual(const EventExpr& ev, SourceLoc loc, Arena& arena);

Expr* EitherEventActual(Expr* lhs, Expr* rhs, Arena& arena);

bool IsEventActual(const Expr* actual);

const PropertyExprNode* ActualTree(const Expr* actual);

std::vector<EventExpr> EventsOfActual(Expr* actual);

void AppendActualEvents(const EventExpr& ev, Expr* actual, Arena& arena,
                        std::vector<EventExpr>& out);

std::string InstanceDeclName(const Expr* instance);

Expr* SelfDeterminedActual(Expr* actual, Arena& arena);

Expr* CastUntypedActual(Expr* actual, TokenKind type_kw, Arena& arena);

bool IsSelfDeterminedCast(const Expr* cast);

bool SamePath(const Expr* a, const Expr* b);

}  // namespace delta
