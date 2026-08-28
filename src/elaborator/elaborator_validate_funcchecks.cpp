#include <format>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §12.7.3 — the leftmost identifier reached by descending an lvalue through
// index selects, member accesses, and increment/decrement operators. Names
// the object an assignment ultimately writes.
static std::string_view LvalueRootName(const Expr* e) {
  while (e) {
    switch (e->kind) {
      case ExprKind::kIdentifier:
        return e->text;
      case ExprKind::kSelect:
        e = e->base;
        break;
      case ExprKind::kMemberAccess:
        e = e->lhs;
        break;
      case ExprKind::kUnary:
      case ExprKind::kPostfixUnary:
        e = e->lhs ? e->lhs : e->base;
        break;
      default:
        return {};
    }
  }
  return {};
}

// §12.7.3 — the identifier naming the array a foreach iterates over. For a
// hierarchical designator (a.b.arr) this is the trailing member name.
static std::string_view ForeachArrayName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess)
    return e->text;
  return {};
}

static bool IsIncDecExpr(const Expr* e) {
  if (!e) return false;
  if (e->kind != ExprKind::kUnary && e->kind != ExprKind::kPostfixUnary)
    return false;
  return e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus;
}

// §12.7.3 — foreach loop variables are read-only. Reports every statement in
// the loop body that assigns to (or increments/decrements) one of `vars`.
static void CheckForeachVarsReadOnly(
    const Stmt* s, const std::unordered_set<std::string_view>& vars,
    DiagEngine& diag) {
  if (!s) return;
  const Expr* target = nullptr;
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      target = s->lhs;
      break;
    case StmtKind::kExprStmt:
      if (IsIncDecExpr(s->expr)) target = s->expr;
      break;
    default:
      break;
  }
  if (target) {
    auto root = LvalueRootName(target);
    if (!root.empty() && vars.count(root)) {
      diag.Error(s->range.start,
                 std::format("foreach loop variable '{}' is read-only and "
                             "cannot be assigned",
                             root),
                 Subclause("12.7.3"));
    }
  }
  // Every member of Stmt that holds a statement, taken from ForEachChildStmt
  // in elaborator_validate_internal.h rather than listed again here. §12.7.3
  // makes the loop variable read-only for the whole of the loop body, so a
  // member this walk misses is a position an assignment to one goes
  // unreported. Nothing stops early: the clause is broken once per write, and
  // each write is reported where it stands.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckForeachVarsReadOnly(sub, vars, diag); });
}

static bool IsIntegralVectorKind(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// §12.7.3 — the number of dimensions a foreach can address on an
// integral/vector array declaration: its packed dimensions plus its unpacked
// dimensions, all of which are visible directly on the declaration.
static int ForeachDimCount(const ModuleItem* decl) {
  int packed = (decl->data_type.packed_dim_left != nullptr ? 1 : 0) +
               static_cast<int>(decl->data_type.extra_packed_dims.size());
  int unpacked = static_cast<int>(decl->unpacked_dims.size());
  return packed + unpacked;
}

// §12.7.3 — applies the foreach-loop semantic rules to a single foreach
// statement `s` (already known to be StmtKind::kForeach).
static void CheckOneForeachStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& arrays,
    DiagEngine& diag) {
  std::string_view arr_name = ForeachArrayName(s->expr);

  std::unordered_set<std::string_view> named_vars;
  for (auto v : s->foreach_vars) {
    if (v.empty()) continue;
    named_vars.insert(v);
    // A loop variable shall not reuse the array's identifier.
    if (!arr_name.empty() && v == arr_name) {
      diag.Error(s->range.start,
                 std::format("foreach loop variable '{}' may not have the "
                             "same name as the array it iterates over",
                             v),
                 Subclause("12.7.3"));
    }
  }

  if (!named_vars.empty()) CheckForeachVarsReadOnly(s->body, named_vars, diag);

  // The loop-variable count may not exceed the array's dimensionality. Only
  // checked for module-level integral/vector arrays whose dimension count is
  // fully determined by the declaration (typedef'd or aggregate types may
  // contribute hidden packed dimensions, so they are left alone).
  auto it = arrays.find(arr_name);
  if (it != arrays.end() && IsIntegralVectorKind(it->second->data_type.kind)) {
    int dims = ForeachDimCount(it->second);
    if (static_cast<int>(s->foreach_vars.size()) > dims) {
      diag.Error(
          s->range.start,
          std::format("foreach lists {} loop variables but array '{}' has "
                      "only {} dimension(s)",
                      s->foreach_vars.size(), arr_name, dims),
          Subclause("12.7.3"));
    }
  }
}

// §12.7.3 — applies the foreach-loop semantic rules to every foreach statement
// reachable from `s`.
static void CheckForeachInStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& arrays,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForeach) CheckOneForeachStmt(s, arrays, diag);
  // Every member of Stmt that holds a statement, taken from ForEachChildStmt
  // in elaborator_validate_internal.h rather than listed again here. A foreach
  // is a statement like any other, so which member holds it says nothing about
  // whether §12.7.3 covers it, and a member this walk misses is a foreach the
  // clause is not applied to.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckForeachInStmt(sub, arrays, diag); });
}

}  // namespace

void Elaborator::ValidateForeachLoops(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> arrays;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      arrays.emplace(item->name, item);
  }
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind) && item->body) {
      CheckForeachInStmt(item->body, arrays, diag_);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts)
        CheckForeachInStmt(s, arrays, diag_);
    }
  }
}

// §13.4.3 says a constant function "shall not contain a statement that
// directly schedules an event to execute after the function has returned" and
// "shall not contain any fork constructs". Neither says where the offending
// statement may stand, so every position a statement holds a statement in is
// one the search has to look at, and BodyContainsStmt takes those positions
// from ForEachChildStmt in elaborator_validate_internal.h rather than listing
// them again. ForEachChildStmt hands the visitor the field itself, so a walk
// that only reads takes a `Stmt* const&`, and it visits every link with no way
// to stop, so the first hit is kept in `found` and the recursion runs only
// while `found` is false.
//
// Stmt::rs_productions is descended with the rest: §18.17.6 gives break and
// return a meaning in a randsequence production code block that they have
// nowhere else, neither is matched here, and A.6.12's rs_code_block holds the
// ordinary procedural statements that do spawn a fork and schedule an event.
// Three links can never be the one that answers and are walked because the
// shared list is walked whole: src/parser/parser_stmt_block.cpp fills
// Stmt::fork_stmts on a StmtKind::kFork alone, which `match` answers at first,
// and A.6.8 admits no fork, nonblocking assignment or timing control in a
// for_initialization or a for_step.
template <typename Match>
static bool BodyContainsStmt(const Stmt* s, Match match) {
  if (!s) return false;
  if (match(s)) return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (!found) found = BodyContainsStmt(sub, match);
  });
  return found;
}

static bool BodyContainsFork(const Stmt* s) {
  return BodyContainsStmt(
      s, [](const Stmt* n) { return n->kind == StmtKind::kFork; });
}

static bool BodyContainsNonblocking(const Stmt* s) {
  return BodyContainsStmt(
      s, [](const Stmt* n) { return n->kind == StmtKind::kNonblockingAssign; });
}

// §13.4.3 (c): every timing-control, waiting and event-trigger statement
// schedules an event to fire after the function has returned, not just the
// nonblocking assignment BodyContainsNonblocking answers for.
static bool SchedulesPostReturnEvent(const Stmt* s) {
  switch (s->kind) {
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kEventControl:
    case StmtKind::kTimingControl:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
    case StmtKind::kWaitOrder:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kExpect:
      return true;
    default:
      return false;
  }
}

static bool BodyContainsEventScheduling(const Stmt* s) {
  return BodyContainsStmt(s, SchedulesPostReturnEvent);
}

// §13.4.3 lets a constant function reference a name "declared locally to the
// current function", and a declaration is local wherever in the body it is
// written, so the collection takes every position a statement holds a statement
// in from ForEachChildStmt in elaborator_validate_internal.h. A position it
// misses is one a name declared there goes uncollected from, and
// CheckConstFuncIdentifier below then reports a reference to that name.
// §18.17.6 is about break and return, which declare nothing, so descending
// Stmt::rs_productions is what §13.4.3 asks for: A.6.12 puts a data_declaration
// at the head of an rs_code_block. Stmt::for_steps holds no declaration, A.6.8
// admitting only an operator_assignment, an inc_or_dec_expression or a call.
static void CollectLocalDeclNames(const Stmt* s,
                                  std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) {
    if (!s->var_name.empty()) out.insert(s->var_name);
  }
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectLocalDeclNames(sub, out); });
}

// §13.4.3 (e) — true when the expr is a `.`-separated path that reaches
// outside the function's own scope (any kMemberAccess whose leftmost LHS is
// not a name the function declared, that isn't a built-in method call).
static const Expr* LeftmostIdentifier(const Expr* e) {
  while (e && e->kind == ExprKind::kMemberAccess) e = e->lhs;
  return e;
}

static bool IsBuiltinMethodOnLocal(
    const Expr* call, const std::unordered_set<std::string_view>& local_names) {
  if (!call || call->kind != ExprKind::kCall) return false;
  if (!call->lhs || call->lhs->kind != ExprKind::kMemberAccess) return false;
  const Expr* root = LeftmostIdentifier(call->lhs);
  if (!root || root->kind != ExprKind::kIdentifier) return false;
  return local_names.count(root->text) > 0;
}

// §13.4.3 — the recursion-invariant scope a constant function is validated
// against: the names visible to its body (module parameters and the set of
// callable function names), the function-declaration map used to recurse into
// nested constant-function calls, the visited-name guard against (mutual)
// recursion, and the diagnostic sink. One scope object threads through the
// whole constant-function check; only `func`, its source location, and the
// per-function set of body-local names vary between calls.
struct ConstFuncScope {
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_map<std::string_view, const ModuleItem*>* func_decls;
  std::unordered_set<std::string_view>* visited;
  DiagEngine& diag;
};

struct ConstFuncBodyCheck {
  std::string_view func_name;
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_set<std::string_view>& local_names;
  const std::unordered_map<std::string_view, const ModuleItem*>* func_decls;
  std::unordered_set<std::string_view>* visited;
  DiagEngine& diag;
  SourceLoc loc;
  bool failed = false;
};

static bool ValidateConstantFunction(const ModuleItem* func, SourceLoc loc,
                                     const ConstFuncScope& scope);

static void WalkConstFuncExpr(const Expr* e, ConstFuncBodyCheck& chk);

static void WalkConstFuncExprChildren(const Expr* e, ConstFuncBodyCheck& chk) {
  WalkConstFuncExpr(e->lhs, chk);
  WalkConstFuncExpr(e->rhs, chk);
  WalkConstFuncExpr(e->condition, chk);
  WalkConstFuncExpr(e->true_expr, chk);
  WalkConstFuncExpr(e->false_expr, chk);
  WalkConstFuncExpr(e->base, chk);
  WalkConstFuncExpr(e->index, chk);
  WalkConstFuncExpr(e->index_end, chk);
  WalkConstFuncExpr(e->repeat_count, chk);
  for (auto* a : e->args) WalkConstFuncExpr(a, chk);
  for (auto* el : e->elements) WalkConstFuncExpr(el, chk);
}

// §13.4.3 (h) — an identifier referenced inside a constant function must name
// the function itself, a local, a parameter, or another function.
static void CheckConstFuncIdentifier(const Expr* e, ConstFuncBodyCheck& chk) {
  if (e->text == chk.func_name) return;
  if (chk.local_names.count(e->text)) return;
  if (chk.param_names.count(e->text)) return;
  if (chk.function_names.count(e->text)) return;
  chk.diag.Error(
      chk.loc,
      std::format(
          "constant function '{}' references identifier '{}' that is not "
          "a parameter, function name, or local declaration",
          chk.func_name, e->text),
      Subclause("13.4.3"));
  chk.failed = true;
}

// §13.4.3 (e) — `.` paths from a non-local root mean a hierarchical reach
// outside the function.
static void CheckConstFuncMemberAccess(const Expr* e, ConstFuncBodyCheck& chk) {
  const Expr* root = LeftmostIdentifier(e);
  if (root && root->kind == ExprKind::kIdentifier &&
      !chk.local_names.count(root->text) &&
      !chk.param_names.count(root->text)) {
    chk.diag.Error(
        chk.loc,
        std::format("constant function '{}' shall not contain hierarchical "
                    "references",
                    chk.func_name),
        Subclause("13.4.3"));
    chk.failed = true;
    return;
  }
  WalkConstFuncExprChildren(e, chk);
}

// §13.4.3 (g) — only the §11.2.1 constant-system-function whitelist is legal
// inside a constant function body. The single carve-out is the elaboration
// severity tasks (§20.10.1), which are statements, not expressions, so they
// are handled when the simulator evaluates the function body.
static void CheckConstFuncSystemCall(const Expr* e, ConstFuncBodyCheck& chk) {
  if (!IsConstantSysFunc(e->callee)) {
    chk.diag.Error(
        chk.loc,
        std::format("constant function '{}' calls non-constant system function "
                    "'{}'",
                    chk.func_name, e->callee),
        Subclause("13.4.3"));
    chk.failed = true;
    return;
  }
  WalkConstFuncExprChildren(e, chk);
}

// §13.4.3 (f) — built-in methods invoked on a local variable are the explicit
// exception in the LRM; otherwise the callee must be a known function so that
// the recursive constant-function check applies.
static void CheckConstFuncCall(const Expr* e, ConstFuncBodyCheck& chk) {
  if (IsBuiltinMethodOnLocal(e, chk.local_names)) {
    for (auto* a : e->args) WalkConstFuncExpr(a, chk);
    return;
  }
  if (!e->callee.empty() && !chk.function_names.count(e->callee) &&
      e->callee != chk.func_name) {
    chk.diag.Error(
        chk.loc,
        std::format(
            "constant function '{}' invokes '{}' which is not a constant "
            "function",
            chk.func_name, e->callee),
        Subclause("13.4.3"));
    chk.failed = true;
    return;
  }
  // The nested callee must itself satisfy the constant-function constraints.
  // Recurse into its body, guarding against direct or mutual recursion by
  // tracking visited names.
  if (!e->callee.empty() && chk.func_decls && chk.visited &&
      e->callee != chk.func_name && !chk.visited->count(e->callee)) {
    auto it = chk.func_decls->find(e->callee);
    if (it != chk.func_decls->end()) {
      ConstFuncScope scope{chk.param_names, chk.function_names, chk.func_decls,
                           chk.visited, chk.diag};
      if (!ValidateConstantFunction(it->second, chk.loc, scope)) {
        chk.failed = true;
        return;
      }
    }
  }
  WalkConstFuncExprChildren(e, chk);
}

static void WalkConstFuncExpr(const Expr* e, ConstFuncBodyCheck& chk) {
  if (!e || chk.failed) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      CheckConstFuncIdentifier(e, chk);
      return;
    case ExprKind::kMemberAccess:
      CheckConstFuncMemberAccess(e, chk);
      return;
    case ExprKind::kSystemCall:
      CheckConstFuncSystemCall(e, chk);
      return;
    case ExprKind::kCall:
      CheckConstFuncCall(e, chk);
      return;
    default:
      WalkConstFuncExprChildren(e, chk);
      return;
  }
}

// The one expression §13.4.3 leaves to the statement it stands in: a system
// task call written as a statement is ignored when the constant function is
// evaluated rather than rejected when it is validated, so the §11.2.1
// constant-system-function whitelist is not put to it and only its arguments
// are walked, for the identifier-scope and hierarchical-reference rules.
// Returns the call for WalkConstFuncStmt to walk that way and to skip when the
// shared expression list hands it over as Stmt::expr.
static const Expr* StatementFormSystemCall(const Stmt* s) {
  if (s->kind != StmtKind::kExprStmt || !s->expr) return nullptr;
  return s->expr->kind == ExprKind::kSystemCall ? s->expr : nullptr;
}

// §13.4.3's rules on what a constant function body may reference — no
// hierarchical reference, no non-constant function invocation, only a constant
// system function, and no identifier that is not a parameter, a function name
// or a local declaration — bar the reference itself and say nothing about
// which of a statement's expressions holds it, so every position a statement
// holds an expression in is one they reach. The walk takes those positions
// from ForEachChildExpr in elaborator_validate_internal.h and the
// child-statement links from ForEachChildStmt beside it, rather than listing
// either again. §18.17.6 is about break and return, neither an expression, so
// descending Stmt::rs_productions is what §13.4.3 asks for. Stmt::fork_stmts is
// walked because the shared lists are walked whole, and no body reaches here
// holding a fork: ValidateConstFuncBodyContent rejects one first.
//
// Two of the positions ForEachChildExpr hands over cannot carry a reference
// this walk reports, and both are visited rather than skipped because the list
// is one list. A.6.5 gives `wait_statement ::= wait_order ( hierarchical_
// identifier { , hierarchical_identifier } ) action_block`, and
// Stmt::wait_order_events is filled for that statement alone, which §13.4.3's
// "shall not contain a statement that directly schedules an event to execute
// after the function has returned" has ValidateConstFuncBodyContent reject
// before this runs. Stmt::cycle_delay is the same: A.6.5 admits a cycle_delay
// in a procedural_timing_control, rejected there as well, and A.6.11 admits
// one in a clocking_drive, which is written with `<=` and so is rejected as a
// nonblocking assignment. A.6.2's blocking_assignment takes a
// delay_or_event_control, which A.6.5 gives no cycle_delay alternative:
// src/parser/parser_stmt.cpp builds that statement anyway, from the intra-
// assignment timing shared with the nonblocking form, and §14.11's "cycle
// delay (##) is not a legal intra-assignment delay" is what answers it.
static void WalkConstFuncStmt(const Stmt* s, ConstFuncBodyCheck& chk) {
  if (!s || chk.failed) return;
  const Expr* sys_call = StatementFormSystemCall(s);
  if (sys_call) {
    for (auto* a : sys_call->args) WalkConstFuncExpr(a, chk);
  }
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (e != sys_call) WalkConstFuncExpr(e, chk);
  });
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkConstFuncStmt(sub, chk); });
}

// §13.4.3 — a constant function may not take output/inout/ref arguments, and
// each default argument value must itself be a constant expression. The
// enclosing scope's parameter/localparam names are made visible so that a
// default value written as a parameter reference (a constant expression per
// §11.2.1) is accepted rather than mistaken for a non-constant. Returns false
// (after reporting) on the first violation.
static bool ValidateConstFuncArgs(
    const ModuleItem* func, SourceLoc loc,
    const std::unordered_set<std::string_view>& param_names, DiagEngine& diag) {
  ScopeMap default_scope;
  for (auto p : param_names) default_scope[p] = 0;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kOutput ||
        arg.direction == Direction::kInout ||
        arg.direction == Direction::kRef) {
      diag.Error(loc,
                 std::format("constant function '{}' shall not have {}"
                             " arguments",
                             func->name,
                             arg.direction == Direction::kOutput  ? "output"
                             : arg.direction == Direction::kInout ? "inout"
                                                                  : "ref"),
                 Subclause("13.4.3"));
      return false;
    }
    // §13.4.3 (k) — a default argument value, if supplied, must itself be a
    // constant expression per §11.2.1.
    if (arg.default_value &&
        !IsConstantExpr(arg.default_value, default_scope)) {
      diag.Error(
          loc,
          std::format(
              "constant function '{}' default value for argument '{}' is not "
              "a constant expression",
              func->name, arg.name),
          Subclause("13.4.3"));
      return false;
    }
  }
  return true;
}

// §13.4.3 (c) — a constant function body may not contain fork, nonblocking
// assignments, or anything that schedules a post-return event. Returns false
// (after reporting) on the first violating top-level body statement.
static bool ValidateConstFuncBodyContent(const ModuleItem* func, SourceLoc loc,
                                         DiagEngine& diag) {
  for (auto* s : func->func_body_stmts) {
    if (BodyContainsFork(s)) {
      diag.Error(loc,
                 std::format("constant function '{}' shall not contain fork",
                             func->name),
                 Subclause("13.4.3"));
      return false;
    }
    if (BodyContainsNonblocking(s)) {
      diag.Error(loc,
                 std::format("constant function '{}' shall not contain "
                             "nonblocking assignments",
                             func->name),
                 Subclause("13.4.3"));
      return false;
    }
    if (BodyContainsEventScheduling(s)) {
      diag.Error(loc,
                 std::format(
                     "constant function '{}' shall not contain statements that "
                     "schedule events to execute after it returns",
                     func->name),
                 Subclause("13.4.3"));
      return false;
    }
  }
  return true;
}

// §13.4.3 — collects the set of names local to a constant function body: each
// named argument, the function's own name (its implicit result variable), and
// every variable declared inside the body.
static std::unordered_set<std::string_view> CollectConstFuncLocalNames(
    const ModuleItem* func) {
  std::unordered_set<std::string_view> local_names;
  for (const auto& arg : func->func_args)
    if (!arg.name.empty()) local_names.insert(arg.name);
  if (!func->name.empty()) local_names.insert(func->name);
  for (auto* s : func->func_body_stmts) CollectLocalDeclNames(s, local_names);
  return local_names;
}

// §13.4.3 — walks the body of a constant function, applying the
// identifier-scope, hierarchical-reference, system-call, and nested-call rules.
// Returns false (the body failed) once any §13.4.3 violation is reported.
static bool CheckConstFuncBody(
    const ModuleItem* func, SourceLoc loc, const ConstFuncScope& scope,
    const std::unordered_set<std::string_view>& local_names) {
  ConstFuncBodyCheck chk{
      func->name,       scope.param_names, scope.function_names, local_names,
      scope.func_decls, scope.visited,     scope.diag,           loc,
      /*failed=*/false};
  for (auto* s : func->func_body_stmts) WalkConstFuncStmt(s, chk);
  return !chk.failed;
}

static bool ValidateConstantFunction(const ModuleItem* func, SourceLoc loc,
                                     const ConstFuncScope& scope) {
  if (scope.visited && !func->name.empty()) {
    if (!scope.visited->insert(func->name).second) return true;
  }
  if (!ValidateConstFuncArgs(func, loc, scope.param_names, scope.diag))
    return false;
  if (!ValidateConstFuncBodyContent(func, loc, scope.diag)) return false;

  std::unordered_set<std::string_view> local_names =
      CollectConstFuncLocalNames(func);
  return CheckConstFuncBody(func, loc, scope, local_names);
}

struct ConstFuncCallCtx {
  const std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_set<std::string_view>& dpi_import_names;
  DiagEngine& diag;
};

// §13.4.3 — the arguments to a constant function call must all be constant
// expressions per §11.2.1. The only names in scope are the enclosing
// (constant) context's parameters; the arguments are otherwise self-contained.
static void CheckConstFuncCallArgs(const Expr* expr, SourceLoc loc,
                                   const ConstFuncCallCtx& ctx) {
  ScopeMap arg_scope;
  for (auto p : ctx.param_names) arg_scope[p] = 0;
  for (auto* a : expr->args) {
    if (a && !IsConstantExpr(a, arg_scope)) {
      ctx.diag.Error(
          loc,
          std::format("constant function call '{}' has a non-constant argument",
                      expr->callee),
          Subclause("13.4.3"));
      break;
    }
  }
}

// Validates a single call node `expr` (already known to be a non-empty-callee
// kCall) used in a constant context, recursing into a resolved callee.
static void ValidateConstFuncCallNode(const Expr* expr, SourceLoc loc,
                                      const ConstFuncCallCtx& ctx) {
  // §13.4.3 (b) — DPI imports cannot be constant functions, so any attempt to
  // invoke one in a constant context is rejected here.
  if (ctx.dpi_import_names.count(expr->callee)) {
    ctx.diag.Error(
        loc,
        std::format("DPI import '{}' shall not be used as a constant function",
                    expr->callee),
        Subclause("13.4.3"));
    return;
  }
  auto it = ctx.func_decls.find(expr->callee);
  if (it == ctx.func_decls.end()) return;
  std::unordered_set<std::string_view> visited;
  ConstFuncScope scope{ctx.param_names, ctx.function_names, &ctx.func_decls,
                       &visited, ctx.diag};
  ValidateConstantFunction(it->second, loc, scope);
  CheckConstFuncCallArgs(expr, loc, ctx);
}

static void ValidateConstantFuncCallsInExpr(const Expr* expr, SourceLoc loc,
                                            const ConstFuncCallCtx& ctx) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    ValidateConstFuncCallNode(expr, loc, ctx);
  }
  ValidateConstantFuncCallsInExpr(expr->lhs, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->rhs, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->condition, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->true_expr, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->false_expr, loc, ctx);
  for (auto* arg : expr->args) ValidateConstantFuncCallsInExpr(arg, loc, ctx);
  for (auto* elem : expr->elements)
    ValidateConstantFuncCallsInExpr(elem, loc, ctx);
}

static void ValidateConstFuncCallsInItems(const std::vector<ModuleItem*>& items,
                                          const ConstFuncCallCtx& ctx);

// Validates constant-function calls within a generate construct's condition
// and all of its nested bodies (then/else/case arms).
static void ValidateConstFuncCallsInGenerate(const ModuleItem* item,
                                             const ConstFuncCallCtx& ctx) {
  if (item->gen_cond) {
    ValidateConstantFuncCallsInExpr(item->gen_cond, item->loc, ctx);
  }
  ValidateConstFuncCallsInItems(item->gen_body, ctx);
  if (item->gen_else) {
    ValidateConstFuncCallsInItems(item->gen_else->gen_body, ctx);
  }
  for (const auto& ci : item->gen_case_items) {
    ValidateConstFuncCallsInItems(ci.body, ctx);
  }
}

static void ValidateConstFuncCallsInItems(const std::vector<ModuleItem*>& items,
                                          const ConstFuncCallCtx& ctx) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      ValidateConstantFuncCallsInExpr(item->init_expr, item->loc, ctx);
      continue;
    }
    if (item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase ||
        item->kind == ModuleItemKind::kGenerateFor) {
      ValidateConstFuncCallsInGenerate(item, ctx);
    }
  }
}

void Elaborator::ValidateConstantFunctionCalls(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> param_names;
  for (const auto& [pname, _] : decl->params) param_names.insert(pname);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl && !item->name.empty())
      param_names.insert(item->name);
  }

  std::unordered_set<std::string_view> function_names;
  for (const auto& [fname, _] : func_decls_) function_names.insert(fname);

  std::unordered_set<std::string_view> dpi_import_names;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kDpiImport && !item->name.empty())
      dpi_import_names.insert(item->name);
  }

  ConstFuncCallCtx ctx{func_decls_, param_names, function_names,
                       dpi_import_names, diag_};

  for (const auto& [name, default_expr] : decl->params) {
    if (default_expr) {
      ValidateConstantFuncCallsInExpr(default_expr, decl->range.start, ctx);
    }
  }
  ValidateConstFuncCallsInItems(decl->items, ctx);
}

}  // namespace delta
