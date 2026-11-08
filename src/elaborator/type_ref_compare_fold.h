#pragma once

#include <cstdint>
#include <functional>
#include <optional>

namespace delta {

struct Expr;
struct ModuleItem;
struct Stmt;

using TypeRefCompareFolder = std::function<std::optional<int64_t>(const Expr*)>;

void FoldTypeRefComparesInExpr(Expr* e, const TypeRefCompareFolder& fold);

bool WritesAnAssignment(const Expr* e);

TypeRefCompareFolder BarringAssignments(const TypeRefCompareFolder& fold);

void FoldTypeRefComparesOfStmt(Stmt* s, const TypeRefCompareFolder& fold);

void FoldItemTypeRefCompares(ModuleItem* item,
                             const TypeRefCompareFolder& fold);

}  // namespace delta
