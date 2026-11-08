#pragma once

namespace delta {

class DiagEngine;
struct ClassDecl;
struct Expr;
struct ModuleItem;

void ReportImplicationOperators(const Expr* expr, DiagEngine& diag);

void ReportItemImplicationOperators(const ModuleItem& item, DiagEngine& diag);

void ReportClassImplicationOperators(const ClassDecl* cls, DiagEngine& diag);

}  // namespace delta
