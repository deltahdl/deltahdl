#pragma once

#include <functional>

#include "common/source_loc.h"

namespace delta {

struct Expr;
struct ExprTypeScope;
struct ModuleItem;
struct Stmt;

bool SelectsDynamicElement(const Expr* e, const ExprTypeScope& scope);

void ForEachTypeRef(const Expr* e,
                    const std::function<void(const Expr*)>& on_ref);

void ForEachTypeRefOfStmt(const Stmt* s,
                          const std::function<void(const Expr*)>& on_ref);

void ForEachItemExprTypeRef(
    const ModuleItem* item,
    const std::function<void(const Expr*, SourceLoc)>& on_ref);

}  // namespace delta
