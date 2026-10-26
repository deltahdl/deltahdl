#pragma once

namespace delta {

class DiagEngine;
struct ClassDecl;
struct Expr;
struct ModuleItem;

// A.8.6 with A.2.10: report each `|->` or `|=>` joining two operands in
// `expr`, an ordinary expression. Both are property operators (§16.12.7), and
// binary_operator, the operators an expression joins two operands with, holds
// neither.
void ReportImplicationOperators(const Expr* expr, DiagEngine& diag);

// The same for the ordinary expressions `item` holds: a continuous
// assignment's, a declaration's initializer or a let's body, a subroutine's or
// a let's port defaults, those of a class it declares, and those of the
// statements its body and its subroutine body hold, the lets declared among a
// block's items included. A concurrent assertion's property and an expect
// statement's are property expressions and are left out; the statements of
// their action blocks are not.
void ReportItemImplicationOperators(const ModuleItem& item, DiagEngine& diag);

// The same for the ordinary expressions of the class `cls`: its parameter
// values, the arguments it hands its base's constructor, and each member's
// initializer, constraints and method, nested classes included.
void ReportClassImplicationOperators(const ClassDecl* cls, DiagEngine& diag);

}  // namespace delta
