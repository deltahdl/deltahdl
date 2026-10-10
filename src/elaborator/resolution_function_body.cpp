#include "elaborator/resolution_function_body.h"

#include <array>
#include <format>
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

// §7.5.3 and §7.10.2 (printed pages 158 and 170): the built-in methods that
// change the size or the contents of a dynamic array or a queue in place.
constexpr std::array<std::string_view, 10> kMutatingMethods = {
    "delete",    "insert", "push_back", "push_front", "pop_back",
    "pop_front", "sort",   "rsort",     "reverse",    "shuffle"};

// What the walk of one resolution function's body compares each write with:
// the function's name, its driver array argument, and every name the function
// declares, which a write may reach without leaving the call.
struct BodyScan {
  std::string_view function;
  std::string_view drivers;
  std::unordered_set<std::string_view> locals;
  DiagEngine& diag;
};

}  // namespace

static void ReportWrite(std::string_view name, SourceLoc loc,
                        const BodyScan& scan) {
  if (name.empty()) return;
  if (name == scan.drivers) {
    scan.diag.Error(loc,
                    std::format("resolution function '{}' writes to or "
                                "resizes its driver array '{}'",
                                scan.function, name),
                    Subclause("6.6.7"));
    return;
  }
  if (scan.locals.count(name) != 0) return;
  scan.diag.Error(loc,
                  std::format("resolution function '{}' has a side effect: it "
                              "writes '{}', which it does not declare",
                              scan.function, name),
                  Subclause("6.6.7"));
}

// The variables an assignment's left side writes: the data object a dotted or
// selected name begins with, and each such name a concatenation gathers.
static void ReportLhsWrites(const Expr* lhs, SourceLoc loc,
                            const BodyScan& scan) {
  if (lhs->kind == ExprKind::kConcatenation) {
    for (const Expr* element : lhs->elements) {
      ReportLhsWrites(element, loc, scan);
    }
    return;
  }
  ReportWrite(LhsBaseName(lhs), loc, scan);
}

// The parser builds every call a statement can make through ParseCallExpr,
// which always records the callee in `lhs`.
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

// An expression statement writes when it increments or decrements a variable
// (§11.4.2) or calls a method that changes an array in place. No operator but
// an increment or decrement carries the `++` or `--` token, so the operator
// alone says which expression is one.
static void ReportExprStmtWrites(const Expr* e, SourceLoc loc,
                                 const BodyScan& scan) {
  if (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus) {
    ReportWrite(LhsBaseName(e->lhs), loc, scan);
    return;
  }
  if (IsMutatingMethodCall(e)) ReportWrite(LhsBaseName(e->lhs->lhs), loc, scan);
}

// ForEachChildStmt hands over every child slot a statement has, the empty ones
// too, such as the else branch of an if written without one.
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
