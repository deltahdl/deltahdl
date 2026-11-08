#include "elaborator/resolution_function_body.h"

#include <array>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

constexpr std::array<std::string_view, 10> kMutatingMethods = {
    "delete",    "insert", "push_back", "push_front", "pop_back",
    "pop_front", "sort",   "rsort",     "reverse",    "shuffle"};

struct BodyScan {
  std::string_view function;
  std::string_view drivers;
  std::unordered_set<std::string_view> locals;
  DiagEngine& diag;
};

}  // namespace

static void ReportSideEffect(std::string_view name, SourceLoc loc,
                             const BodyScan& scan) {
  scan.diag.Error(loc,
                  std::format("resolution function '{}' has a side effect: it "
                              "writes '{}', which it does not declare",
                              scan.function, name),
                  Subclause("6.6.7"));
}

static const Expr* TargetHead(const Expr* e) {
  for (;;) {
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
    } else if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      e = e->lhs;
    } else {
      return e;
    }
  }
}

static std::string TargetName(const Expr* e) {
  if (e->kind == ExprKind::kSelect) return TargetName(e->base);
  if (e->kind == ExprKind::kMemberAccess) {
    return TargetName(e->lhs) + (e->is_scope_resolution ? "::" : ".") +
           std::string(e->rhs->text);
  }
  if (e->scope_prefix.empty()) return std::string(e->text);
  return std::string(e->scope_prefix) +
         (e->scope_prefix == "$root" ? "." : "::") + std::string(e->text);
}

static void ReportWrite(const Expr* target, SourceLoc loc,
                        const BodyScan& scan) {
  const Expr* head = TargetHead(target);
  if (head->kind == ExprKind::kMemberAccess || !head->scope_prefix.empty()) {
    ReportSideEffect(TargetName(target), loc, scan);
    return;
  }
  if (head->text == scan.drivers) {
    scan.diag.Error(loc,
                    std::format("resolution function '{}' writes to or "
                                "resizes its driver array '{}'",
                                scan.function, head->text),
                    Subclause("6.6.7"));
    return;
  }
  if (scan.locals.count(head->text) != 0) return;
  ReportSideEffect(head->text, loc, scan);
}

static void ReportLhsWrites(const Expr* lhs, SourceLoc loc,
                            const BodyScan& scan) {
  if (lhs->kind == ExprKind::kConcatenation) {
    for (const Expr* element : lhs->elements) {
      ReportLhsWrites(element, loc, scan);
    }
    return;
  }
  ReportWrite(lhs, loc, scan);
}

static bool IsMutatingMethodCall(const Expr* e) {
  if (e->kind != ExprKind::kCall || e->lhs->kind != ExprKind::kMemberAccess ||
      e->lhs->is_scope_resolution) {
    return false;
  }
  for (std::string_view method : kMutatingMethods) {
    if (e->lhs->rhs->text == method) return true;
  }
  return false;
}

static void ReportExprStmtWrites(const Expr* e, SourceLoc loc,
                                 const BodyScan& scan) {
  if (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus) {
    ReportWrite(e->lhs, loc, scan);
    return;
  }
  if (IsMutatingMethodCall(e)) ReportWrite(e->lhs->lhs, loc, scan);
}

static void ScanStmt(const Stmt* s, const BodyScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    ReportLhsWrites(s->lhs, s->range.start, scan);
  } else if (s->kind == StmtKind::kExprStmt) {
    ReportExprStmtWrites(s->expr, s->range.start, scan);
  }
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { ScanStmt(sub, scan); });
}

void CheckResolutionFunctionBody(const ModuleItem* fn, DiagEngine& diag) {
  if (fn->func_args.empty()) return;
  BodyScan scan{fn->name, fn->func_args.front().name, {fn->name}, diag};
  for (const auto& arg : fn->func_args) scan.locals.insert(arg.name);
  for (const Stmt* s : fn->func_body_stmts) {
    CollectProcLocalNames(s, scan.locals);
  }
  for (const Stmt* s : fn->func_body_stmts) ScanStmt(s, scan);
}

}  // namespace delta
