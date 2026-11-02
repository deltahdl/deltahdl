#pragma once

#include <functional>

namespace delta {

struct Expr;
struct ExprTypeScope;
struct Stmt;

// §6.23: whether the expression `e` a type reference names selects, at any
// depth, an element of a dynamic object: a dynamic array (§7.5), a queue
// (§7.10) or an associative array (§7.8). A select is judged by the type of
// the value it is applied to, each name read as `scope` declares it, whose
// array tables are given: a name,
// a dimension of a multidimensional array after the first (§7.4.5), a member
// of a structure (§7.2), a property read through a class handle (§8.5), a
// value whose type is a typedef naming an array, and the queue an array
// locator method gives (§7.12.1).
bool SelectsDynamicElement(const Expr* e, const ExprTypeScope& scope);

// Shows `on_ref` each type reference the expression `e` writes, at any depth.
void ForEachTypeRef(const Expr* e,
                    const std::function<void(const Expr*)>& on_ref);

// Shows `on_ref` each type reference the expressions the statement `s`, which
// is not null, itself writes hold: its targets and values, its condition, its
// assertion, a case item's expressions and a declaration's initializer. The
// statements `s` holds are not among them.
void ForEachTypeRefOfStmt(const Stmt* s,
                          const std::function<void(const Expr*)>& on_ref);

}  // namespace delta
