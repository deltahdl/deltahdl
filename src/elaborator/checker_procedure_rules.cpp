#include "elaborator/checker_procedure_rules.h"

#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

// The names of the items of `kind` the checker body declares.
NameSet DeclaredNames(const ModuleDecl* decl, ModuleItemKind kind) {
  NameSet names;
  for (const auto* item : decl->items) {
    if (item->kind == kind && !item->name.empty()) names.insert(item->name);
  }
  return names;
}

// §17.6: a declaration in a checker procedure whose type names one of the
// checker's covergroups, `automatic cg cg_1 = new();`, instantiates it there.
void WalkForCovergroupInstances(const Stmt* s, const NameSet& covergroups,
                                DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl &&
      covergroups.count(s->var_decl_type.type_name) != 0) {
    diag.Error(s->range.start,
               std::format("covergroup '{}' cannot be instantiated in a "
                           "procedure of a checker; instantiate it in the "
                           "checker body",
                           s->var_decl_type.type_name),
               Subclause("17.6"));
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkForCovergroupInstances(sub, covergroups, diag);
  });
}

// §16.6's kinds of argument, which §17.8 applies to a function called on a
// checker variable's right-hand side; a formal written without a direction
// takes the one before it, the first input (§13.3).
bool HasArgumentWrittenBack(const ModuleItem* fn) {
  Direction dir = Direction::kInput;
  for (const FunctionArg& arg : fn->func_args) {
    if (arg.direction != Direction::kNone) dir = arg.direction;
    FunctionArgKind kind = FunctionArgKind::kInput;
    if (dir == Direction::kOutput) kind = FunctionArgKind::kOutput;
    if (dir == Direction::kInout) kind = FunctionArgKind::kInout;
    if (dir == Direction::kRef) {
      kind = arg.is_const ? FunctionArgKind::kConstRef : FunctionArgKind::kRef;
    }
    if (!FunctionArgKindAllowedInAssertionExpr(kind)) return true;
  }
  return false;
}

// §17.8: each call in `e` of one of the functions `writers` names.
void ReportWritingCalls(const Expr* e, const NameSet& writers,
                        DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall && writers.count(e->callee) != 0) {
    diag.Error(e->range.start,
               std::format("function '{}' has an output, inout or ref "
                           "argument and cannot be called on the right-hand "
                           "side of a checker variable assignment",
                           e->callee),
               Subclause("17.8"));
  }
  ForEachExprChild(
      e, [&](const Expr* child) { ReportWritingCalls(child, writers, diag); });
}

void WalkForWritingCalls(const Stmt* s, const NameSet& writers,
                         DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    ReportWritingCalls(s->rhs, writers, diag);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkForWritingCalls(sub, writers, diag); });
}

}  // namespace

void ValidateCheckerProcedureCovergroups(const ModuleDecl* decl,
                                         DiagEngine& diag) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  NameSet covergroups = DeclaredNames(decl, ModuleItemKind::kCovergroupDecl);
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkForCovergroupInstances(item->body, covergroups, diag);
    }
  }
}

void ValidateCheckerAssignmentCalls(const ModuleDecl* decl, DiagEngine& diag) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  NameSet writers;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl &&
        HasArgumentWrittenBack(item)) {
      writers.insert(item->name);
    }
  }
  // A continuous assignment is left to §13.4, which bars such a function
  // from one wherever it is written.
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkForWritingCalls(item->body, writers, diag);
    }
  }
}

}  // namespace delta
