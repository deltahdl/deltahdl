#include <format>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

void CheckJumpRules(const Stmt* s, int loop_depth, int fork_depth,
                    bool in_subroutine, DiagEngine& diag);

// Returns true when `s` is itself a jump leaf (break/continue/return) and
// reports any §12.8 violation for it. Caller stops descending on true.
bool CheckJumpLeaf(const Stmt* s, int loop_depth, int fork_depth,
                   bool in_subroutine, DiagEngine& diag) {
  switch (s->kind) {
    case StmtKind::kBreak:
      if (loop_depth == 0) {
        if (fork_depth > 0) {
          diag.Error(s->range.start,
                     "break inside fork-join cannot exit a loop outside the "
                     "fork-join block");
        } else {
          diag.Error(s->range.start, "break statement is not inside a loop");
        }
      }
      return true;
    case StmtKind::kContinue:
      if (loop_depth == 0) {
        if (fork_depth > 0) {
          diag.Error(s->range.start,
                     "continue inside fork-join cannot affect a loop outside "
                     "the fork-join block");
        } else {
          diag.Error(s->range.start, "continue statement is not inside a loop");
        }
      }
      return true;
    case StmtKind::kReturn:
      if (!in_subroutine) {
        diag.Error(s->range.start,
                   "return statement is only allowed inside a subroutine");
      }
      return true;
    default:
      return false;
  }
}

bool IsLoopStmtKind(StmtKind k) {
  return k == StmtKind::kFor || k == StmtKind::kForeach ||
         k == StmtKind::kWhile || k == StmtKind::kForever ||
         k == StmtKind::kRepeat || k == StmtKind::kDoWhile;
}

// Recurses into every generic child statement of `s` carrying the current
// jump-context depths unchanged (used for non-loop, non-fork statements).
void CheckJumpRulesChildren(const Stmt* s, int loop_depth, int fork_depth,
                            bool in_subroutine, DiagEngine& diag) {
  for (auto* sub : s->stmts)
    CheckJumpRules(sub, loop_depth, fork_depth, in_subroutine, diag);
  CheckJumpRules(s->then_branch, loop_depth, fork_depth, in_subroutine, diag);
  CheckJumpRules(s->else_branch, loop_depth, fork_depth, in_subroutine, diag);
  for (auto& ci : s->case_items)
    CheckJumpRules(ci.body, loop_depth, fork_depth, in_subroutine, diag);
  for (auto& ri : s->randcase_items)
    CheckJumpRules(ri.second, loop_depth, fork_depth, in_subroutine, diag);
  CheckJumpRules(s->assert_pass_stmt, loop_depth, fork_depth, in_subroutine,
                 diag);
  CheckJumpRules(s->assert_fail_stmt, loop_depth, fork_depth, in_subroutine,
                 diag);
}

// Walks one statement subtree enforcing §12.8 rules for break, continue, and
// return. `loop_depth` counts loops reachable from this point without
// crossing a fork-join boundary; `fork_depth` counts enclosing fork-joins.
// `in_subroutine` is true when the walk originated in a function or task body.
void CheckJumpRules(const Stmt* s, int loop_depth, int fork_depth,
                    bool in_subroutine, DiagEngine& diag) {
  if (!s) return;

  if (CheckJumpLeaf(s, loop_depth, fork_depth, in_subroutine, diag)) return;

  if (IsLoopStmtKind(s->kind)) {
    int next_loop = loop_depth + 1;
    CheckJumpRules(s->body, next_loop, fork_depth, in_subroutine, diag);
    CheckJumpRules(s->for_body, next_loop, fork_depth, in_subroutine, diag);
    for (auto* init : s->for_inits)
      CheckJumpRules(init, loop_depth, fork_depth, in_subroutine, diag);
    for (auto* step : s->for_steps)
      CheckJumpRules(step, loop_depth, fork_depth, in_subroutine, diag);
    return;
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts)
      CheckJumpRules(sub, 0, fork_depth + 1, in_subroutine, diag);
    return;
  }

  CheckJumpRulesChildren(s, loop_depth, fork_depth, in_subroutine, diag);
}

// Map literal expression kinds whose type is obvious from the syntax alone
// to the corresponding DataTypeKind. Returns kImplicit when no narrow
// classification is possible without full expression type inference.
DataTypeKind ObviousLiteralKind(const Expr* e) {
  if (!e) return DataTypeKind::kImplicit;
  switch (e->kind) {
    case ExprKind::kStringLiteral:
      return DataTypeKind::kString;
    case ExprKind::kRealLiteral:
      return DataTypeKind::kReal;
    case ExprKind::kIntegerLiteral:
      return DataTypeKind::kInt;
    case ExprKind::kTimeLiteral:
      return DataTypeKind::kTime;
    default:
      return DataTypeKind::kImplicit;
  }
}

// In a value-returning function, a return statement shall carry an
// expression of the correct type. The void-with-expression case is
// reported elsewhere; the type check here catches narrow but clearly
// wrong mismatches (string-vs-integral, real-vs-string, etc.).
void CheckValueReturningFuncReturn(const Stmt* s, std::string_view func_name,
                                   const DataType& return_type,
                                   DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    if (s->expr == nullptr) {
      diag.Error(s->range.start,
                 std::format("return statement in non-void function '{}' "
                             "shall have an expression",
                             func_name));
      return;
    }
    DataTypeKind expr_kind = ObviousLiteralKind(s->expr);
    if (expr_kind != DataTypeKind::kImplicit) {
      DataType expr_type;
      expr_type.kind = expr_kind;
      if (!IsAssignmentCompatible(return_type, expr_type)) {
        diag.Error(s->range.start,
                   std::format("return expression in function '{}' is not "
                               "assignment-compatible with the function's "
                               "return type",
                               func_name));
      }
    }
    return;
  }
  for (auto* sub : s->stmts)
    CheckValueReturningFuncReturn(sub, func_name, return_type, diag);
  for (auto* sub : s->fork_stmts)
    CheckValueReturningFuncReturn(sub, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->then_branch, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->else_branch, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->body, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->for_body, func_name, return_type, diag);
  for (auto& ci : s->case_items)
    CheckValueReturningFuncReturn(ci.body, func_name, return_type, diag);
  for (auto& ri : s->randcase_items)
    CheckValueReturningFuncReturn(ri.second, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->assert_pass_stmt, func_name, return_type,
                                diag);
  CheckValueReturningFuncReturn(s->assert_fail_stmt, func_name, return_type,
                                diag);
}

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
                             root));
    }
  }
  for (auto* sub : s->stmts) CheckForeachVarsReadOnly(sub, vars, diag);
  CheckForeachVarsReadOnly(s->then_branch, vars, diag);
  CheckForeachVarsReadOnly(s->else_branch, vars, diag);
  CheckForeachVarsReadOnly(s->body, vars, diag);
  CheckForeachVarsReadOnly(s->for_body, vars, diag);
  for (auto* sub : s->for_inits) CheckForeachVarsReadOnly(sub, vars, diag);
  for (auto* sub : s->for_steps) CheckForeachVarsReadOnly(sub, vars, diag);
  for (auto* sub : s->fork_stmts) CheckForeachVarsReadOnly(sub, vars, diag);
  for (auto& ci : s->case_items) CheckForeachVarsReadOnly(ci.body, vars, diag);
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
                             v));
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
                      s->foreach_vars.size(), arr_name, dims));
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
  for (auto* sub : s->stmts) CheckForeachInStmt(sub, arrays, diag);
  CheckForeachInStmt(s->then_branch, arrays, diag);
  CheckForeachInStmt(s->else_branch, arrays, diag);
  CheckForeachInStmt(s->body, arrays, diag);
  CheckForeachInStmt(s->for_body, arrays, diag);
  for (auto* sub : s->for_inits) CheckForeachInStmt(sub, arrays, diag);
  for (auto* sub : s->for_steps) CheckForeachInStmt(sub, arrays, diag);
  for (auto* sub : s->fork_stmts) CheckForeachInStmt(sub, arrays, diag);
  for (auto& ci : s->case_items) CheckForeachInStmt(ci.body, arrays, diag);
}

// True for the procedural-block module items (initial/final/always*) whose
// jump and foreach rules are checked against their single `body` statement.
static bool IsProceduralBlock(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kInitialBlock ||
         item->kind == ModuleItemKind::kFinalBlock ||
         item->kind == ModuleItemKind::kAlwaysBlock ||
         item->kind == ModuleItemKind::kAlwaysCombBlock ||
         item->kind == ModuleItemKind::kAlwaysFFBlock ||
         item->kind == ModuleItemKind::kAlwaysLatchBlock;
}

// §12.8 — applies the jump rules to a function/task body and, for a
// value-returning function, also checks each return statement's expression.
static void CheckSubroutineJumpRules(const ModuleItem* item, DiagEngine& diag) {
  bool is_value_returning = false;
  if (item->kind == ModuleItemKind::kFunctionDecl) {
    is_value_returning = (item->return_type.kind != DataTypeKind::kVoid);
  }
  for (auto* s : item->func_body_stmts) {
    CheckJumpRules(s, 0, 0, /*in_subroutine=*/true, diag);
    if (is_value_returning) {
      CheckValueReturningFuncReturn(s, item->name, item->return_type, diag);
    }
  }
}

}  // namespace

void Elaborator::ValidateForeachLoops(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> arrays;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      arrays.emplace(item->name, item);
  }
  for (const auto* item : decl->items) {
    if (IsProceduralBlock(item) && item->body) {
      CheckForeachInStmt(item->body, arrays, diag_);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts)
        CheckForeachInStmt(s, arrays, diag_);
    }
  }
}

void Elaborator::ValidateJumpStatements(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralBlock(item) && item->body) {
      CheckJumpRules(item->body, 0, 0, /*in_subroutine=*/false, diag_);
      continue;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      CheckSubroutineJumpRules(item, diag_);
    }
  }
}

static bool BodyContainsFork(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kFork) return true;
  for (auto* sub : s->stmts)
    if (BodyContainsFork(sub)) return true;
  if (BodyContainsFork(s->then_branch)) return true;
  if (BodyContainsFork(s->else_branch)) return true;
  if (BodyContainsFork(s->body)) return true;
  if (BodyContainsFork(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (BodyContainsFork(ci.body)) return true;
  return false;
}

static bool BodyContainsNonblocking(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kNonblockingAssign) return true;
  for (auto* sub : s->stmts)
    if (BodyContainsNonblocking(sub)) return true;
  if (BodyContainsNonblocking(s->then_branch)) return true;
  if (BodyContainsNonblocking(s->else_branch)) return true;
  if (BodyContainsNonblocking(s->body)) return true;
  if (BodyContainsNonblocking(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (BodyContainsNonblocking(ci.body)) return true;
  return false;
}

// §13.4.3 (c): a constant function may not contain anything that schedules
// an event to fire after the function has returned — that covers every
// timing-control / waiting / event-trigger statement, not just nonblocking
// assignments.
static bool BodyContainsEventScheduling(const Stmt* s) {
  if (!s) return false;
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
      break;
  }
  for (auto* sub : s->stmts)
    if (BodyContainsEventScheduling(sub)) return true;
  if (BodyContainsEventScheduling(s->then_branch)) return true;
  if (BodyContainsEventScheduling(s->else_branch)) return true;
  if (BodyContainsEventScheduling(s->body)) return true;
  if (BodyContainsEventScheduling(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (BodyContainsEventScheduling(ci.body)) return true;
  return false;
}

static void CollectLocalDeclNames(const Stmt* s,
                                  std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) {
    if (!s->var_name.empty()) out.insert(s->var_name);
  }
  for (auto* sub : s->stmts) CollectLocalDeclNames(sub, out);
  CollectLocalDeclNames(s->then_branch, out);
  CollectLocalDeclNames(s->else_branch, out);
  CollectLocalDeclNames(s->body, out);
  CollectLocalDeclNames(s->for_body, out);
  for (auto* init : s->for_inits) CollectLocalDeclNames(init, out);
  for (auto& ci : s->case_items) CollectLocalDeclNames(ci.body, out);
  for (auto* fs : s->fork_stmts) CollectLocalDeclNames(fs, out);
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

static bool ValidateConstantFunction(
    const ModuleItem* func, SourceLoc loc,
    const std::unordered_set<std::string_view>& param_names,
    const std::unordered_set<std::string_view>& function_names,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_decls,
    std::unordered_set<std::string_view>* visited, DiagEngine& diag);

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
          chk.func_name, e->text));
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
                    chk.func_name));
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
                    chk.func_name, e->callee));
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
            chk.func_name, e->callee));
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
      if (!ValidateConstantFunction(it->second, chk.loc, chk.param_names,
                                    chk.function_names, chk.func_decls,
                                    chk.visited, chk.diag)) {
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

static void WalkConstFuncStmt(const Stmt* s, ConstFuncBodyCheck& chk) {
  if (!s || chk.failed) return;
  WalkConstFuncExpr(s->condition, chk);
  WalkConstFuncExpr(s->lhs, chk);
  WalkConstFuncExpr(s->rhs, chk);
  // §13.4.3: system task calls within a constant function are ignored at
  // evaluation time rather than rejected at validation time. A bare
  // statement-form system call is therefore not subjected to the §11.2.1
  // sys-func whitelist; only its arguments are walked for identifier-scope
  // and hierarchical-reference checks.
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kSystemCall) {
    for (auto* a : s->expr->args) WalkConstFuncExpr(a, chk);
  } else {
    WalkConstFuncExpr(s->expr, chk);
  }
  WalkConstFuncExpr(s->delay, chk);
  WalkConstFuncExpr(s->for_cond, chk);
  WalkConstFuncExpr(s->repeat_event_count, chk);
  WalkConstFuncExpr(s->assert_expr, chk);
  WalkConstFuncExpr(s->var_init, chk);
  for (auto* sub : s->stmts) WalkConstFuncStmt(sub, chk);
  WalkConstFuncStmt(s->then_branch, chk);
  WalkConstFuncStmt(s->else_branch, chk);
  WalkConstFuncStmt(s->body, chk);
  WalkConstFuncStmt(s->for_body, chk);
  for (auto* init : s->for_inits) WalkConstFuncStmt(init, chk);
  for (auto* step : s->for_steps) WalkConstFuncStmt(step, chk);
  for (auto& ci : s->case_items) {
    for (auto* pat : ci.patterns) WalkConstFuncExpr(pat, chk);
    WalkConstFuncStmt(ci.body, chk);
  }
}

// §13.4.3 — a constant function may not take output/inout/ref arguments, and
// each default argument value must itself be a constant expression. Returns
// false (after reporting) on the first violation.
static bool ValidateConstFuncArgs(const ModuleItem* func, SourceLoc loc,
                                  DiagEngine& diag) {
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
                                                                  : "ref"));
      return false;
    }
    // §13.4.3 (k) — a default argument value, if supplied, must itself be a
    // constant expression per §11.2.1.
    if (arg.default_value && !IsConstantExpr(arg.default_value)) {
      diag.Error(
          loc,
          std::format(
              "constant function '{}' default value for argument '{}' is not "
              "a constant expression",
              func->name, arg.name));
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
                             func->name));
      return false;
    }
    if (BodyContainsNonblocking(s)) {
      diag.Error(loc, std::format("constant function '{}' shall not contain "
                                  "nonblocking assignments",
                                  func->name));
      return false;
    }
    if (BodyContainsEventScheduling(s)) {
      diag.Error(loc,
                 std::format(
                     "constant function '{}' shall not contain statements that "
                     "schedule events to execute after it returns",
                     func->name));
      return false;
    }
  }
  return true;
}

static bool ValidateConstantFunction(
    const ModuleItem* func, SourceLoc loc,
    const std::unordered_set<std::string_view>& param_names,
    const std::unordered_set<std::string_view>& function_names,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_decls,
    std::unordered_set<std::string_view>* visited, DiagEngine& diag) {
  if (visited && !func->name.empty()) {
    if (!visited->insert(func->name).second) return true;
  }
  if (!ValidateConstFuncArgs(func, loc, diag)) return false;
  if (!ValidateConstFuncBodyContent(func, loc, diag)) return false;

  std::unordered_set<std::string_view> local_names;
  for (const auto& arg : func->func_args)
    if (!arg.name.empty()) local_names.insert(arg.name);
  if (!func->name.empty()) local_names.insert(func->name);
  for (auto* s : func->func_body_stmts) CollectLocalDeclNames(s, local_names);

  ConstFuncBodyCheck chk{func->name,  param_names, function_names,
                         local_names, func_decls,  visited,
                         diag,        loc,         /*failed=*/false};
  for (auto* s : func->func_body_stmts) WalkConstFuncStmt(s, chk);
  return !chk.failed;
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
                      expr->callee));
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
                    expr->callee));
    return;
  }
  auto it = ctx.func_decls.find(expr->callee);
  if (it == ctx.func_decls.end()) return;
  std::unordered_set<std::string_view> visited;
  ValidateConstantFunction(it->second, loc, ctx.param_names, ctx.function_names,
                           &ctx.func_decls, &visited, ctx.diag);
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
