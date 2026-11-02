#pragma once

#include <cstdint>
#include <functional>
#include <optional>

namespace delta {

struct Expr;
struct ModuleItem;
struct Stmt;

using TypeRefCompareFolder = std::function<std::optional<int64_t>(const Expr*)>;

// Hands `fold` each comparison of type references `e` writes.
void FoldTypeRefComparesInExpr(Expr* e, const TypeRefCompareFolder& fold);

// Whether `e` writes an assignment operator.
bool WritesAnAssignment(const Expr* e);

// `fold` where an assignment operator is barred.
TypeRefCompareFolder BarringAssignments(const TypeRefCompareFolder& fold);

// Hands `fold` each comparison of type references the statement `s` writes in
// its own expressions -- its case items' among them, and a declaration's
// initializer -- leaving those of the statements it holds.
void FoldTypeRefComparesOfStmt(Stmt* s, const TypeRefCompareFolder& fold);

// Hands `fold` each comparison of type references `item` writes outside a
// procedure where a value is read while the design runs.
void FoldItemTypeRefCompares(ModuleItem* item,
                             const TypeRefCompareFolder& fold);

}  // namespace delta
