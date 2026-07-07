#include "elaborator/sensitivity.h"

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "parser/ast.h"

namespace delta {

static void CollectSelectReads(const Expr* expr,
                               std::unordered_set<std::string>& out) {
  out.insert(LongestStaticPrefix(expr));

  const Expr* cur = expr;
  while (cur && cur->kind == ExprKind::kSelect) {
    if (cur->index && cur->index->kind != ExprKind::kIntegerLiteral) {
      CollectExprReads(cur->index, out);
    }
    cur = cur->base;
  }
}

void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.insert(std::string(expr->text));
    return;
  }
  if (expr->kind == ExprKind::kSelect) {
    CollectSelectReads(expr, out);
    return;
  }
  if (expr->kind == ExprKind::kCall) {
    // A call contributes to the implicit sensitivity list only through its
    // argument expressions. The callee reference itself adds nothing: a plain
    // function name is neither a net nor a variable, and a reference to a class
    // object on which a method is invoked (or a class scope-resolved name)
    // contributes only via the arguments passed to the call.
    for (auto* arg : expr->args) CollectExprReads(arg, out);
    return;
  }
  CollectExprReads(expr->lhs, out);
  CollectExprReads(expr->rhs, out);
  CollectExprReads(expr->condition, out);
  CollectExprReads(expr->true_expr, out);
  CollectExprReads(expr->false_expr, out);
  CollectExprReads(expr->base, out);
  CollectExprReads(expr->index, out);
  for (auto* arg : expr->args) CollectExprReads(arg, out);
  for (auto* elem : expr->elements) CollectExprReads(elem, out);
}

static void CollectLhsIndexReads(const Expr* lhs,
                                 std::unordered_set<std::string>& out) {
  const Expr* cur = lhs;
  while (cur && cur->kind == ExprKind::kSelect) {
    if (cur->index) CollectExprReads(cur->index, out);
    cur = cur->base;
  }
}

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    CollectLhsIndexReads(stmt->lhs, out);
  }
  if (stmt->kind != StmtKind::kWait) {
    CollectExprReads(stmt->condition, out);
  }
  CollectExprReads(stmt->rhs, out);
  CollectExprReads(stmt->expr, out);
  CollectExprReads(stmt->for_cond, out);
  for (auto* s : stmt->stmts) CollectStmtReads(s, out);
  CollectStmtReads(stmt->then_branch, out);
  CollectStmtReads(stmt->else_branch, out);
  CollectStmtReads(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectStmtReads(fi, out);
  for (auto* fs : stmt->for_steps) CollectStmtReads(fs, out);
  CollectStmtReads(stmt->body, out);
  for (auto* s : stmt->fork_stmts) CollectStmtReads(s, out);
  for (const auto& ci : stmt->case_items) {
    for (const auto* pat : ci.patterns) CollectExprReads(pat, out);
    CollectStmtReads(ci.body, out);
  }
  CollectExprReads(stmt->assert_expr, out);
}

std::vector<std::string> CollectReadSignals(const Stmt* body) {
  std::unordered_set<std::string> set;
  CollectStmtReads(body, set);
  return {set.begin(), set.end()};
}

static void CollectAssignLhsName(const Expr* lhs,
                                 std::unordered_set<std::string>& out) {
  if (!lhs) return;
  const Expr* e = lhs;
  while (e->kind == ExprKind::kSelect && e->base) e = e->base;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty())
    out.insert(std::string(e->text));
}

void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    CollectAssignLhsName(stmt->lhs, out);
  }
  for (const auto* s : stmt->stmts) CollectWrittenNames(s, out);
  CollectWrittenNames(stmt->then_branch, out);
  CollectWrittenNames(stmt->else_branch, out);
  CollectWrittenNames(stmt->body, out);
  CollectWrittenNames(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectWrittenNames(fi, out);
  for (auto* fs : stmt->for_steps) CollectWrittenNames(fs, out);
  for (const auto& ci : stmt->case_items) CollectWrittenNames(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectWrittenNames(s, out);
}

static void CollectBlockLocalNames(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kVarDecl && !stmt->var_name.empty()) {
    out.insert(std::string(stmt->var_name));
  }
  for (const auto* s : stmt->stmts) CollectBlockLocalNames(s, out);
  CollectBlockLocalNames(stmt->then_branch, out);
  CollectBlockLocalNames(stmt->else_branch, out);
  CollectBlockLocalNames(stmt->body, out);
  CollectBlockLocalNames(stmt->for_body, out);
  for (const auto& ci : stmt->case_items) CollectBlockLocalNames(ci.body, out);
}

static void CollectCallNamesFromExpr(
    const Expr* expr, std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    out.insert(expr->callee);
  }
  CollectCallNamesFromExpr(expr->lhs, out);
  CollectCallNamesFromExpr(expr->rhs, out);
  CollectCallNamesFromExpr(expr->condition, out);
  CollectCallNamesFromExpr(expr->true_expr, out);
  CollectCallNamesFromExpr(expr->false_expr, out);
  CollectCallNamesFromExpr(expr->base, out);
  CollectCallNamesFromExpr(expr->index, out);
  for (auto* arg : expr->args) CollectCallNamesFromExpr(arg, out);
  for (auto* elem : expr->elements) CollectCallNamesFromExpr(elem, out);
}

static void CollectCallNamesFromStmt(
    const Stmt* stmt, std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  if (stmt->kind != StmtKind::kWait) {
    CollectCallNamesFromExpr(stmt->condition, out);
  }
  CollectCallNamesFromExpr(stmt->rhs, out);
  CollectCallNamesFromExpr(stmt->expr, out);
  CollectCallNamesFromExpr(stmt->for_cond, out);
  CollectCallNamesFromExpr(stmt->assert_expr, out);
  for (auto* s : stmt->stmts) CollectCallNamesFromStmt(s, out);
  CollectCallNamesFromStmt(stmt->then_branch, out);
  CollectCallNamesFromStmt(stmt->else_branch, out);
  CollectCallNamesFromStmt(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectCallNamesFromStmt(fi, out);
  for (auto* fs : stmt->for_steps) CollectCallNamesFromStmt(fs, out);
  CollectCallNamesFromStmt(stmt->body, out);
  for (auto* s : stmt->fork_stmts) CollectCallNamesFromStmt(s, out);
  for (const auto& ci : stmt->case_items)
    CollectCallNamesFromStmt(ci.body, out);
}

static std::unordered_set<std::string_view> ResolveCalledFunctions(
    const Stmt* body, const FuncMap& funcs) {
  std::unordered_set<std::string_view> visited;
  std::unordered_set<std::string_view> pending;
  CollectCallNamesFromStmt(body, pending);
  while (!pending.empty()) {
    std::unordered_set<std::string_view> next;
    for (auto& name : pending) {
      if (visited.count(name)) continue;
      auto it = funcs.find(name);
      if (it == funcs.end()) continue;
      visited.insert(name);
      for (auto* s : it->second->func_body_stmts) {
        CollectCallNamesFromStmt(s, next);
      }
    }
    pending = std::move(next);
  }
  return visited;
}

static void MergeOneCalledFunctionReads(
    const ModuleItem* func, std::unordered_set<std::string>& reads) {
  for (auto* s : func->func_body_stmts) {
    CollectStmtReads(s, reads);
  }
}

static void MergeOneCalledFunctionLocals(
    const ModuleItem* func, std::unordered_set<std::string>& locals) {
  for (const auto& arg : func->func_args) {
    if (!arg.name.empty()) locals.insert(std::string(arg.name));
  }
  for (auto* s : func->func_body_stmts) {
    CollectBlockLocalNames(s, locals);
  }
}

static void MergeOneCalledFunctionWritten(
    const ModuleItem* func, std::unordered_set<std::string>& written) {
  for (auto* s : func->func_body_stmts) {
    CollectWrittenNames(s, written);
  }
}

// The three signal-name accumulators collected while inferring an implicit
// sensitivity list (IEEE 1800 §9.2.2.2.1, @* / @(*)): identifiers read by the
// process (reads), identifiers that are block-local declarations or formal
// arguments and therefore excluded (locals), and identifiers written by the
// process when self-trigger suppression is requested (written). They describe
// one domain object -- the signal classification of a process body -- so they
// travel together.
struct SignalSets {
  std::unordered_set<std::string> reads;
  std::unordered_set<std::string> locals;
  std::unordered_set<std::string> written;
};

static void MergeCalledFunctionSignals(const Stmt* body, const FuncMap& funcs,
                                       bool exclude_written, SignalSets& sigs) {
  auto called = ResolveCalledFunctions(body, funcs);
  for (auto& fname : called) {
    auto it = funcs.find(fname);
    if (it == funcs.end()) continue;
    const auto* func = it->second;
    MergeOneCalledFunctionReads(func, sigs.reads);
    MergeOneCalledFunctionLocals(func, sigs.locals);
    if (exclude_written) {
      MergeOneCalledFunctionWritten(func, sigs.written);
    }
  }
}

// §9.2.2.2.1: the inferred sensitivity watches whole signals, so reduce a
// read's longest static prefix (e.g. "state[0]", "s.f") to the base identifier.
// The event signal is then a plain identifier that the simulator resolves to
// the declared net/variable (it keys watchers by the base name via
// FindVariable); an indexed/membered text would never match and the process
// would not wake.
static std::string_view BaseSignalName(std::string_view name) {
  auto pos = name.find_first_of("[.");
  return pos == std::string_view::npos ? name : name.substr(0, pos);
}

static std::vector<EventExpr> BuildSensitivityEvents(
    const std::unordered_set<std::string>& reads,
    const std::unordered_set<std::string>& locals,
    const std::unordered_set<std::string>& written, bool exclude_written,
    const std::unordered_set<std::string_view>* const_names, Arena& arena) {
  std::vector<EventExpr> events;
  events.reserve(reads.size());
  // The read names retain their longest static prefix for the locals/written
  // exclusion checks (§9.2.2.2.1), but several selects of one signal collapse
  // to a single base-name event, so dedupe the emitted identifiers.
  std::unordered_set<std::string_view> emitted;
  for (const auto& name : reads) {
    if (locals.count(name)) continue;
    if (exclude_written && written.count(name)) continue;
    std::string_view base = BaseSignalName(name);
    // §9.2.2.2.1: only nets and variables populate the list. A read of a
    // parameter/localparam/specparam (the base of the prefix, or a constant
    // select index that survived as its own read) is dropped -- a constant
    // never changes, so it cannot be part of a sensitivity list.
    if (const_names && const_names->count(base)) continue;
    if (base.empty() || !emitted.insert(base).second) continue;
    auto* expr = arena.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = std::string_view(arena.AllocString(base.data(), base.size()),
                                  base.size());
    events.push_back({Edge::kNone, expr});
  }
  return events;
}

std::vector<EventExpr> InferSensitivity(
    const Stmt* body, Arena& arena, const FuncMap* funcs, bool exclude_written,
    const std::unordered_set<std::string_view>* const_names) {
  SignalSets sigs;
  CollectStmtReads(body, sigs.reads);
  CollectBlockLocalNames(body, sigs.locals);
  if (exclude_written) {
    CollectWrittenNames(body, sigs.written);
  }

  if (funcs && !funcs->empty()) {
    MergeCalledFunctionSignals(body, *funcs, exclude_written, sigs);
  }

  return BuildSensitivityEvents(sigs.reads, sigs.locals, sigs.written,
                                exclude_written, const_names, arena);
}

}  // namespace delta
