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
// a let's port defaults, an instance's parameter values, a gate's or a
// primitive's terminals, a generate construct's header, those of a class or a
// covergroup it declares, and those of the statements its body and its
// subroutine body hold, the lets declared among a block's items included. An
// instance's port connections are left to the elaboration of the instance,
// which knows whether it instantiates a checker. A concurrent assertion's
// property and an expect statement's are property expressions and are left out;
// the statements of their action blocks are not.
void ReportItemImplicationOperators(const ModuleItem& item, DiagEngine& diag);

// The same for the ordinary expressions of the class `cls`: its parameter
// values, the arguments it hands its base's constructor, and each member's
// initializer, constraints, method and embedded covergroup, nested classes
// included.
void ReportClassImplicationOperators(const ClassDecl* cls, DiagEngine& diag);

}  // namespace delta
