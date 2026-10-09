#include "elaborator/elaborator_call_targets.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// The names a walk of one module's procedures sees as variables or nets: the
// module's own, and those each block around the statement walked declares,
// the innermost last (§23.9); and the other names the module itself declares,
// or imports as data, which a call statement cannot call.
struct DataScope {
  std::unordered_set<std::string_view> module;
  std::vector<std::string_view> blocks;
  std::unordered_set<std::string_view> uncallable;

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::find(blocks, name) != blocks.end();
  }
};

// Reports a call of `name` written at `loc` where the scope sees the name as
// a variable or a net.
void ReportIfData(std::string_view name, SourceLoc loc, const DataScope& scope,
                  DiagEngine& diag) {
  if (!scope.Names(name)) return;
  diag.Error(loc,
             std::format("'{}' names a variable or a net, and a call names a "
                         "task or a function",
                         name),
             Subclause("A.8.2"));
}

// The plain name the call `expr` calls, null where `expr` is no call by a
// plain name. A constructor call is none: its `lhs` is the object a shallow
// copy copies, `new src` (§8.12).
const Expr* NamedCallee(const Expr& expr) {
  const bool kNamed = expr.kind == ExprKind::kCall && expr.lhs != nullptr &&
                      expr.text != "new" &&
                      expr.lhs->kind == ExprKind::kIdentifier;
  return kNamed ? expr.lhs : nullptr;
}

// A.6.9: a call statement, `x;` or `x(...);`, whose name the scope declares
// as no task or function: a variable or a net (A.8.2), or anything else the
// module declares or imports as data, such as a parameter, a let or a
// sequence. A name the module does not declare may name a task or function of
// an instance above it (§23.8), and is left alone.
void ReportStatementCall(const Stmt& stmt, const DataScope& scope,
                         DiagEngine& diag) {
  const bool kBare = stmt.expr->kind == ExprKind::kIdentifier;
  const Expr* callee = kBare ? stmt.expr : NamedCallee(*stmt.expr);
  if (callee == nullptr) return;
  const std::string_view kName = callee->text;
  if (scope.Names(kName)) {
    // A call with an argument list naming data is the expression walk's.
    if (kBare) ReportIfData(kName, stmt.range.start, scope, diag);
    return;
  }
  if (!scope.uncallable.contains(kName)) return;
  diag.Error(stmt.range.start,
             std::format("'{}' names no task or function, and a call "
                         "statement calls one",
                         kName),
             Subclause("A.6.9"));
}

// Each call by a plain name `expr` holds, itself included.
void CheckExprCalls(const Expr* expr, const DataScope& scope,
                    DiagEngine& diag) {
  if (expr == nullptr) return;
  if (const Expr* callee = NamedCallee(*expr)) {
    ReportIfData(callee->text, expr->range.start, scope, diag);
  }
  ForEachExprChild(
      expr, [&](const Expr* child) { CheckExprCalls(child, scope, diag); });
}

// The calls `stmt` and the statements it holds make by a plain name: a bare
// call statement, `x;`, and each call an expression of theirs holds, with the
// variables a block declares in scope over the statements the block holds.
void CheckStmtCalls(const Stmt* stmt, DataScope& scope, DiagEngine& diag) {
  if (stmt == nullptr) return;
  const std::size_t kOuter = scope.blocks.size();
  if (stmt->kind == StmtKind::kBlock || stmt->kind == StmtKind::kFork) {
    const std::vector<Stmt*>& items =
        stmt->kind == StmtKind::kFork ? stmt->fork_stmts : stmt->stmts;
    for (const Stmt* item : items) {
      if (item->kind == StmtKind::kVarDecl)
        scope.blocks.push_back(item->var_name);
    }
  }
  if (stmt->kind == StmtKind::kExprStmt) {
    ReportStatementCall(*stmt, scope, diag);
  }
  ForEachChildExpr(
      stmt, [&](const Expr* expr) { CheckExprCalls(expr, scope, diag); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CheckStmtCalls(sub, scope, diag); });
  scope.blocks.resize(kOuter);
}

// Whether `item` declares a task or a function a call may call: one the
// source writes, or one a DPI import or export names (§35.5).
bool IsSubroutineItem(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kTaskDecl ||
         item.kind == ModuleItemKind::kFunctionDecl ||
         item.kind == ModuleItemKind::kDpiImport ||
         item.kind == ModuleItemKind::kDpiExport;
}

// §26.3: the variables and nets the package `import` names brings in, by its
// item name or with a wildcard, added to `names`.
void AddImportedData(const CompilationUnit& unit, const ImportItem& import,
                     std::unordered_set<std::string_view>& names) {
  for (const PackageDecl* package : unit.packages) {
    if (package->name != import.package_name) continue;
    for (const ModuleItem* item : package->items) {
      const bool kData = item->kind == ModuleItemKind::kVarDecl ||
                         item->kind == ModuleItemKind::kNetDecl;
      if (kData && (import.is_wildcard || item->name == import.item_name)) {
        names.insert(item->name);
      }
    }
  }
}

}  // namespace

void ReportCallsOfDataNames(const ModuleDecl& decl, const CompilationUnit& unit,
                            DiagEngine& diag) {
  DataScope scope;
  std::unordered_set<std::string_view> subroutines;
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      scope.module.insert(item->name);
    } else if (IsSubroutineItem(*item)) {
      subroutines.insert(item->name);
    } else if (!item->name.empty()) {
      scope.uncallable.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kImportDecl) {
      AddImportedData(unit, item->import_item, scope.uncallable);
    }
  }
  // A name a DPI export gives a function the module also declares stays
  // callable whichever item the walk met first.
  for (std::string_view name : subroutines) scope.uncallable.erase(name);
  for (const ModuleItem* item : decl.items) {
    if (IsProceduralItemKind(item->kind))
      CheckStmtCalls(item->body, scope, diag);
  }
}

}  // namespace delta
