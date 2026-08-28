#include "elaborator/sensitivity.h"

#include <unordered_set>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_internal.h"
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

// True when `sub` is one of the two statements of `owner`'s assertion action
// block. §9.2.2.2.1 (printed page 223) says "Expressions used in assertion
// action blocks do not contribute to the implicit sensitivity list of an
// always_comb", and its example has the always_comb trigger on b, c and e while
// `disable_error`, read in the else branch of `A1:assert (a != e) else if
// (!disable_error) $error("failed");`, stays out. So the two walks that collect
// reads stop at these, and the two that collect writes and block-local
// declarations do not: exception (b) is about where a name is written and
// exception (a) about where one is declared, and neither is a rule about what
// contributes.
//
// The sentence before it puts the asserted expression itself in the list, "as
// if that expression were used as a condition of an if statement", which is
// Stmt::assert_expr and is read directly rather than through this descent.
bool IsAssertionActionBlock(const Stmt* owner, const Stmt* sub) {
  return sub != nullptr &&
         (sub == owner->assert_pass_stmt || sub == owner->assert_fail_stmt);
}

// §9.2.2.2.1 takes the longest static prefix of every net or variable read
// within the block. Its three exceptions name no statement position, and the
// one position the clause does exclude is the assertion action block
// IsAssertionActionBlock above answers for, so a read counts wherever else a
// statement holds a statement.
//
// ForEachChildStmt in elaborator_validate_internal.h states those thirteen
// positions, once for the whole elaborator, which is why the list is not
// written out again here. It hands the visitor the field itself, so a walk that
// only reads the tree takes a `Stmt* const&`.
//
// The expression fields are read one by one rather than through the
// ForEachChildExpr beside it, because exception (c) excludes an identifier that
// appears only in a timing control expression and not reading those fields is
// how this function implements it. ForEachChildExpr hands over Stmt::delay,
// Stmt::cycle_delay, Stmt::events, Stmt::repeat_event_count and
// Stmt::wait_order_events along with the rest, giving the visitor no way to
// tell a timing control expression from an ordinary one; a wait statement's
// condition is skipped here for the same reason. The positions read are
// Stmt::condition, Stmt::rhs, Stmt::expr, Stmt::for_cond, Stmt::assert_expr,
// Stmt::var_init, the weight of each Stmt::randcase_items entry and the
// patterns of each Stmt::case_items entry.
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
  CollectExprReads(stmt->assert_expr, out);
  // A.2.4 gives a variable_decl_assignment an initializer, which the parser
  // keeps in Stmt::var_init. It is an ordinary expression and not a timing
  // control, so exception (c) leaves what it reads in the list, and exception
  // (a) removes the name being declared rather than the names its initializer
  // reads.
  CollectExprReads(stmt->var_init, out);
  // §18.16 makes a randcase weight an expression the statement evaluates:
  // "The randcase weights can be arbitrary expressions, not just constants",
  // and its example weighs branches by `a + b` over two byte variables, each
  // weight expression being "evaluated at most once" per execution. A variable
  // named there is therefore read within the block, and no exception of
  // §9.2.2.2.1 removes it. That is the same answer WalkStmtCaseIdents in
  // elaborator_scope_rules.cpp gives the position for §26.3.
  for (const auto& rc : stmt->randcase_items) CollectExprReads(rc.first, out);
  // The case-item bodies are statements the descent below reaches; the patterns
  // are expressions it does not, so they are read here.
  for (const auto& ci : stmt->case_items) {
    for (const auto* pat : ci.patterns) CollectExprReads(pat, out);
  }
  ForEachChildStmt(stmt, [stmt, &out](Stmt* const& sub) {
    if (IsAssertionActionBlock(stmt, sub)) return;
    CollectStmtReads(sub, out);
  });
}

static void CollectAssignLhsName(const Expr* lhs,
                                 std::unordered_set<std::string>& out) {
  if (!lhs) return;
  const Expr* e = lhs;
  while (e->kind == ExprKind::kSelect && e->base) e = e->base;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty())
    out.insert(std::string(e->text));
}

// §9.2.2.2.1 exception (b) leaves out of the list any expression also written
// within the block, and names no statement position either, so a write counts
// wherever a statement holds a statement. A write this walk does not reach is a
// name the exception does not remove, which puts the process's own output in
// its sensitivity list and re-triggers it on its own assignment.
//
// The positions come from ForEachChildStmt in
// elaborator_validate_internal.h, stated there once for the whole elaborator.
void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    CollectAssignLhsName(stmt->lhs, out);
  }
  ForEachChildStmt(stmt,
                   [&out](Stmt* const& sub) { CollectWrittenNames(sub, out); });
}

// §9.2.2.2.1 exception (a) leaves out of the list any expansion of a variable
// declared within the block, and names no statement position, so a declaration
// counts wherever a statement holds a statement. A.6.3 admits a
// block_item_declaration at the head of every seq_block, and a seq_block stands
// in each of those positions, so a declaration this walk does not reach is a
// block-local name the exception does not remove and the list then carries a
// name no net or variable of the design answers to.
//
// The positions come from ForEachChildStmt in elaborator_validate_internal.h,
// stated there once for the whole elaborator.
static void CollectBlockLocalNames(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kVarDecl && !stmt->var_name.empty()) {
    out.insert(std::string(stmt->var_name));
  }
  ForEachChildStmt(
      stmt, [&out](Stmt* const& sub) { CollectBlockLocalNames(sub, out); });
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

// §9.2.2.2.1 counts a read "within any function called within the block", and
// puts no condition on where in the block the call stands, so a call counts
// wherever a statement holds a statement. A call this walk does not reach
// contributes none of the called function's reads.
//
// The positions come from ForEachChildStmt in
// elaborator_validate_internal.h, and the expressions are read one by one for
// the reason CollectStmtReads above gives.
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
  // Stmt::var_init and a randcase weight are expressions the block evaluates,
  // for the reasons CollectStmtReads above gives, so a function called from
  // either is called within the block and contributes its own reads.
  CollectCallNamesFromExpr(stmt->var_init, out);
  for (const auto& rc : stmt->randcase_items) {
    CollectCallNamesFromExpr(rc.first, out);
  }
  ForEachChildStmt(stmt, [stmt, &out](Stmt* const& sub) {
    if (IsAssertionActionBlock(stmt, sub)) return;
    CollectCallNamesFromStmt(sub, out);
  });
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
    const SignalSets& sigs, bool exclude_written,
    const std::unordered_set<std::string_view>* const_names, Arena& arena) {
  std::vector<EventExpr> events;
  events.reserve(sigs.reads.size());
  // The read names retain their longest static prefix for the locals/written
  // exclusion checks (§9.2.2.2.1), but several selects of one signal collapse
  // to a single base-name event, so dedupe the emitted identifiers.
  std::unordered_set<std::string_view> emitted;
  for (const auto& name : sigs.reads) {
    if (sigs.locals.count(name)) continue;
    if (exclude_written && sigs.written.count(name)) continue;
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

  return BuildSensitivityEvents(sigs, exclude_written, const_names, arena);
}

}  // namespace delta
