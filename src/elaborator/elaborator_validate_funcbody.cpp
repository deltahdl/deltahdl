#include <format>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);
void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

static void CheckNoReturnInFork(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    diag.Error(s->range.start,
               "return statement is not allowed inside a fork-join block",
               Subclause("9.3.2"));
    return;
  }
  for (auto* sub : s->stmts) CheckNoReturnInFork(sub, diag);
  for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  CheckNoReturnInFork(s->then_branch, diag);
  CheckNoReturnInFork(s->else_branch, diag);
  CheckNoReturnInFork(s->body, diag);
  CheckNoReturnInFork(s->for_body, diag);
  for (auto& ci : s->case_items) CheckNoReturnInFork(ci.body, diag);
  for (auto& ri : s->randcase_items) CheckNoReturnInFork(ri.second, diag);
  CheckNoReturnInFork(s->assert_pass_stmt, diag);
  CheckNoReturnInFork(s->assert_fail_stmt, diag);
}

static void CheckExprForRefArgs(
    const Expr* e, const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier && ref_names.count(e->text)) {
    diag.Error(e->range.start,
               std::format("ref argument '{}' cannot be used inside a "
                           "fork-join_any or fork-join_none block",
                           e->text),
               Subclause("9.3.2"));
    return;
  }
  CheckExprForRefArgs(e->lhs, ref_names, diag);
  CheckExprForRefArgs(e->rhs, ref_names, diag);
  CheckExprForRefArgs(e->condition, ref_names, diag);
  CheckExprForRefArgs(e->true_expr, ref_names, diag);
  CheckExprForRefArgs(e->false_expr, ref_names, diag);
  CheckExprForRefArgs(e->base, ref_names, diag);
  CheckExprForRefArgs(e->index, ref_names, diag);
  CheckExprForRefArgs(e->index_end, ref_names, diag);
  CheckExprForRefArgs(e->with_expr, ref_names, diag);
  CheckExprForRefArgs(e->repeat_count, ref_names, diag);
  for (auto* arg : e->args) CheckExprForRefArgs(arg, ref_names, diag);
  for (auto* elem : e->elements) CheckExprForRefArgs(elem, ref_names, diag);
}

static void CheckStmtExprsForRefArgs(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!is_fork_block_item || s->kind != StmtKind::kVarDecl)
    CheckExprForRefArgs(s->var_init, ref_names, diag);
  CheckExprForRefArgs(s->expr, ref_names, diag);
  CheckExprForRefArgs(s->lhs, ref_names, diag);
  CheckExprForRefArgs(s->rhs, ref_names, diag);
  CheckExprForRefArgs(s->delay, ref_names, diag);
  CheckExprForRefArgs(s->cycle_delay, ref_names, diag);
  CheckExprForRefArgs(s->condition, ref_names, diag);
  CheckExprForRefArgs(s->for_cond, ref_names, diag);
  CheckExprForRefArgs(s->assert_expr, ref_names, diag);
  CheckExprForRefArgs(s->repeat_event_count, ref_names, diag);
  for (auto* dim : s->var_unpacked_dims)
    CheckExprForRefArgs(dim, ref_names, diag);
  for (auto& ev : s->events) {
    CheckExprForRefArgs(ev.signal, ref_names, diag);
    CheckExprForRefArgs(ev.iff_condition, ref_names, diag);
  }
  for (auto& ci : s->case_items)
    for (auto* p : ci.patterns) CheckExprForRefArgs(p, ref_names, diag);
  for (auto& ri : s->randcase_items)
    CheckExprForRefArgs(ri.first, ref_names, diag);
  for (auto* we : s->wait_order_events)
    CheckExprForRefArgs(we, ref_names, diag);
}

// §9.3.2 forbids a ref argument anywhere inside a fork-join_any or
// fork-join_none block, and puts no condition on the position the use is
// written in, so every position a statement holds a statement in is one the
// rule reaches. ForEachChildStmt in elaborator_validate_internal.h states
// those positions once for the whole elaborator, which is why the list is not
// written out again here.
//
// The recursion passes false for is_fork_block_item because the flag answers
// for a statement the fork holds directly. §9.3.2 excepts "the initialization
// value expressions of variables declared in a block_item_declaration of the
// fork", and A.6.3 puts a block_item_declaration among the fork's own items,
// so no statement nested below one is that declaration.
static void CheckStmtForRefArgs(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!s) return;
  CheckStmtExprsForRefArgs(s, ref_names, is_fork_block_item, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckStmtForRefArgs(sub, ref_names, false, diag);
  });
}

// Finds the fork-join_any and fork-join_none blocks §9.3.2 governs. A.6.3
// makes a par_block a statement, and the clause puts no condition on where the
// fork stands, so every position a statement holds a statement in is one such
// a fork can be written in. ForEachChildStmt in
// elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
//
// Stmt::for_inits and Stmt::for_steps are walked because the shared list is
// walked whole, and no conforming source puts a fork in either: A.6.8 admits
// only a list_of_variable_assignments or a for_variable_declaration in a
// for_initialization, and only an operator_assignment, an
// inc_or_dec_expression or a function_subroutine_call in a for_step, none of
// which is a par_block.
static void CheckRefArgsInForkBlocks(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kFork && (s->join_kind == TokenKind::kKwJoinAny ||
                                     s->join_kind == TokenKind::kKwJoinNone)) {
    for (auto* fs : s->fork_stmts) {
      bool is_block_item = (fs->kind == StmtKind::kVarDecl);
      CheckStmtForRefArgs(fs, ref_names, is_block_item, diag);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckRefArgsInForkBlocks(sub, ref_names, diag);
  });
}

static void CheckFuncBodyTimeControl(const Stmt* s, DiagEngine& diag) {
  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kCycleDelay ||
      s->kind == StmtKind::kEventControl ||
      s->kind == StmtKind::kTimingControl || s->kind == StmtKind::kWait ||
      s->kind == StmtKind::kWaitFork || s->kind == StmtKind::kWaitOrder ||
      s->kind == StmtKind::kExpect) {
    diag.Error(s->range.start,
               "time-controlling statement is not allowed inside a function",
               Subclause("13.4"));
  }
}

static void CheckFuncBodyVarDecl(const Stmt* s, std::string_view func_name,
                                 DiagEngine& diag) {
  if (s->kind != StmtKind::kVarDecl) return;
  if (!func_name.empty() && s->var_name == func_name) {
    diag.Error(s->range.start,
               std::format("declaration of '{}' conflicts with function name",
                           func_name),
               Subclause("13.4.1"));
  }
  // A static variable's initializer is deliberately not checked for
  // constancy. §6.8 permits a run-time initial value in as many words:
  // "Initial values are not constrained to simple constants; they can include
  // run-time expressions, including dynamic memory allocation", and names
  // calling $urandom as one of its own examples. §6.21 constrains only when
  // that initialization runs, once at the beginning of simulation, and
  // §13.4.2 covers storage and reentrancy, so neither narrows §6.8 for a
  // static variable declared inside a subroutine.
}

static void CheckFuncBodyStmtSelf(
    const Stmt* s, bool is_void,
    const std::unordered_set<std::string_view>& task_names,
    std::string_view func_name, DiagEngine& diag) {
  if (s->kind == StmtKind::kReturn && s->expr && is_void) {
    diag.Error(s->range.start, "void function returns a value",
               Subclause("13.4.1"));
  }
  if (s->kind == StmtKind::kFork && s->join_kind != TokenKind::kKwJoinNone) {
    diag.Error(s->range.start,
               "only fork/join_none is permitted inside a function",
               Subclause("13.4"));
  }

  CheckFuncBodyTimeControl(s, diag);

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall &&
      task_names.count(s->expr->callee) != 0) {
    diag.Error(s->range.start, "function cannot enable a task",
               Subclause("13.4"));
  }

  CheckFuncBodyVarDecl(s, func_name, diag);

  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }
}

static void CheckFuncBodyStmt(
    const Stmt* s, bool is_void,
    const std::unordered_set<std::string_view>& task_names,
    std::string_view func_name, DiagEngine& diag) {
  if (!s) return;
  CheckFuncBodyStmtSelf(s, is_void, task_names, func_name, diag);

  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone)
    return;
  for (auto* sub : s->stmts)
    CheckFuncBodyStmt(sub, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->then_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->else_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->for_body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->assert_pass_stmt, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->assert_fail_stmt, is_void, task_names, func_name, diag);
  for (auto& ci : s->case_items)
    CheckFuncBodyStmt(ci.body, is_void, task_names, func_name, diag);
  for (auto& ri : s->randcase_items)
    CheckFuncBodyStmt(ri.second, is_void, task_names, func_name, diag);
}

// §13.3.2: an automatic task variable is deallocated when the invocation ends,
// so a reference to one must not outlive the call. Walk an expression tree
// looking for any leaf identifier naming such a variable.
static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars);

static bool AnyChildExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,       e->base,       e->index,     e->index_end,
      e->condition, e->true_expr, e->false_expr, e->with_expr, e->repeat_count};
  for (const Expr* child : kChildren)
    if (ExprRefsAutoVar(child, auto_vars)) return true;
  for (auto* a : e->args)
    if (ExprRefsAutoVar(a, auto_vars)) return true;
  for (auto* el : e->elements)
    if (ExprRefsAutoVar(el, auto_vars)) return true;
  return false;
}

static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty() &&
      auto_vars.count(e->text) != 0)
    return true;
  return AnyChildExprRefsAutoVar(e, auto_vars);
}

// Which clause forbids the four uses below, and how a report names the
// variable. §13.3.1 says "Specific local variables can be declared as
// automatic within a static task or as static within an automatic task", so a
// task-local variable is deallocated when the task returns for either of two
// reasons, and the clause that forbids these uses of it differs with the
// reason.
//
// A variable of an automatic task is what §13.3.2's four bullets are about:
// they open "Because variables declared in automatic tasks are deallocated at
// the end of the task invocation, they shall not be used in certain constructs
// that might refer to them after that point", and reach nothing else.
//
// A variable a static task declares `automatic` is not one, and answers to
// §6.21. Its first sentence forbids writing an automatic variable "with
// nonblocking, continuous, or procedural continuous assignments", which is the
// nonblocking assignment and the procedural continuous assignment. Its last
// sentence, "References to automatic variables and elements or members of
// dynamic variables shall be limited to procedural blocks", is what the other
// two break: an intra-assignment event control defers its evaluation past the
// statement, and $monitor keeps reading its arguments for the rest of the
// simulation, so neither reference stays inside the block that declared the
// variable.
//
// ValidateTaskBody is the only place that knows which task declared the
// variables, so the rule travels from there rather than being fixed at a site.
struct AutoVarRule {
  std::string_view variable;
  Subclause subclause;
};

constexpr AutoVarRule kAutomaticTaskVar{"automatic task variable",
                                        Subclause("13.3.2")};
constexpr AutoVarRule kAutomaticVarInStaticTask{"automatic variable",
                                                Subclause("6.21")};

// §13.3.2: the nonblocking-assignment restriction applies to a write into an
// automatic task variable's own storage, including a bit-select or part-select
// of it. A bit/part-select chain is walked down to its root name. Member access
// is deliberately not traversed: it denotes a write through a handle or
// reference whose target outlives the automatic variable.
static std::string_view NbaAutoTargetRoot(const Expr* e) {
  while (e && e->kind == ExprKind::kSelect) e = e->base;
  if (e && e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

// An automatic task variable shall not appear in the intra-assignment event
// control of a nonblocking assignment, since the event control can defer
// evaluation past the variable's lifetime.
static void CheckNbaEventControlForAutoVar(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  bool in_event_control = ExprRefsAutoVar(s->repeat_event_count, auto_vars);
  for (const auto& ev : s->events) {
    if (ExprRefsAutoVar(ev.signal, auto_vars) ||
        ExprRefsAutoVar(ev.iff_condition, auto_vars)) {
      in_event_control = true;
    }
  }
  if (in_event_control) {
    diag.Error(s->range.start,
               std::format("{} in intra-assignment event control of "
                           "nonblocking assignment",
                           rule.variable),
               rule.subclause);
  }
}

static void CheckTaskBodyNbaForAutoVar(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (s->kind != StmtKind::kNonblockingAssign) return;
  if (s->lhs) {
    auto target = NbaAutoTargetRoot(s->lhs);
    if (!target.empty() && auto_vars.count(target) != 0) {
      diag.Error(s->range.start,
                 std::format("{} in nonblocking assignment", rule.variable),
                 rule.subclause);
    }
  }
  CheckNbaEventControlForAutoVar(s, auto_vars, rule, diag);
}

// An automatic task variable shall not be traced by continuous monitoring
// system tasks such as $monitor and $dumpvars, whose tracing outlives the
// invocation.
static void CheckTaskBodyMonitorTrace(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (s->kind != StmtKind::kExprStmt || !s->expr ||
      s->expr->kind != ExprKind::kSystemCall ||
      (s->expr->callee != "$monitor" && s->expr->callee != "$dumpvars"))
    return;
  for (auto* a : s->expr->args) {
    if (ExprRefsAutoVar(a, auto_vars)) {
      diag.Error(s->range.start,
                 std::format("{} traced by system task", rule.variable),
                 rule.subclause);
      break;
    }
  }
}

static void CheckTaskBodyContAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(
          s->range.start,
          std::format("{} in procedural continuous assignment", rule.variable),
          rule.subclause);
    }
  }
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }
}

static void CheckTaskBodyStmtSelf(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (s->kind == StmtKind::kReturn && s->expr) {
    diag.Error(s->range.start, "task returns a value", Subclause("13.3"));
  }

  CheckTaskBodyNbaForAutoVar(s, auto_vars, rule, diag);
  CheckTaskBodyMonitorTrace(s, auto_vars, rule, diag);
  CheckTaskBodyContAssign(s, auto_vars, rule, diag);

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }
}

static void CheckTaskBodyStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (!s) return;
  CheckTaskBodyStmtSelf(s, auto_vars, rule, diag);
  for (auto* sub : s->stmts) CheckTaskBodyStmt(sub, auto_vars, rule, diag);
  for (auto* sub : s->fork_stmts) CheckTaskBodyStmt(sub, auto_vars, rule, diag);
  CheckTaskBodyStmt(s->then_branch, auto_vars, rule, diag);
  CheckTaskBodyStmt(s->else_branch, auto_vars, rule, diag);
  CheckTaskBodyStmt(s->body, auto_vars, rule, diag);
  CheckTaskBodyStmt(s->for_body, auto_vars, rule, diag);
  for (auto& ci : s->case_items)
    CheckTaskBodyStmt(ci.body, auto_vars, rule, diag);
}

// Collects the names §6.21 and §13.3.2 govern. §6.21 says "Automatic variables
// and elements of dynamically sized array variables shall not be written with
// nonblocking, continuous, or procedural continuous assignments" and §13.3.2
// opens "Because variables declared in automatic tasks are deallocated at the
// end of the task invocation", so each turns on how a variable was declared and
// neither on where the declaration stands. A.2.8 makes a data_declaration a
// block_item_declaration, so a declaration this collects can be reached through
// every position a statement holds a statement in. ForEachChildStmt in
// elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
//
// Stmt::for_inits and Stmt::for_steps are walked because the shared list is
// walked whole, and neither ever holds a declaration this collects.
// Parser::ParseAssignmentOrExprNoSemi in src/parser/parser_stmt.cpp builds
// every statement in both, and it produces a blocking assignment, a nonblocking
// assignment or an expression statement and never a StmtKind::kVarDecl; a
// control variable declared local to the loop leaves its type in
// Stmt::for_init_types and its name in the assignment.
static void CollectAutoVarNames(const Stmt* s, bool task_is_auto,
                                std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    if ((task_is_auto && !s->var_is_static) ||
        (!task_is_auto && s->var_is_automatic)) {
      out.insert(s->var_name);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectAutoVarNames(sub, task_is_auto, out);
  });
}

static void ValidateFunctionArgDecls(
    const ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  for (const auto& arg : item->func_args) {
    if (arg.data_type.kind == DataTypeKind::kNamed &&
        arg.data_type.type_name == "weak_reference" &&
        !arg.data_type.type_params.empty()) {
      const auto& tp = arg.data_type.type_params[0];
      if (!WeakRefTypeParamNamesClass(tp, typedefs, class_names)) {
        diag.Error(item->loc,
                   "weak_reference type parameter shall be a class type",
                   Subclause("8.30.1"));
      }
    }
    if (arg.default_value && !item->is_ansi_ports) {
      diag.Error(item->loc,
                 std::format("default argument values are only allowed with "
                             "ANSI-style port declarations for '{}'",
                             arg.name),
                 Subclause("13.5.3"));
    }
  }
}

static void ValidateRefArgsInForkBlocks(const ModuleItem* item,
                                        DiagEngine& diag) {
  std::unordered_set<std::string_view> ref_names;
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef && !arg.is_ref_static) {
      ref_names.insert(arg.name);
    }
  }
  if (!ref_names.empty()) {
    for (auto* s : item->func_body_stmts)
      CheckRefArgsInForkBlocks(s, ref_names, diag);
  }
}

static void ValidateTaskBody(const ModuleItem* item, DiagEngine& diag) {
  bool is_auto = item->is_automatic;

  std::unordered_set<std::string_view> auto_vars;
  if (is_auto) {
    for (const auto& arg : item->func_args) {
      auto_vars.insert(arg.name);
    }
  }
  for (auto* s : item->func_body_stmts) {
    CollectAutoVarNames(s, is_auto, auto_vars);
  }
  const AutoVarRule& rule =
      is_auto ? kAutomaticTaskVar : kAutomaticVarInStaticTask;
  for (auto* s : item->func_body_stmts) {
    CheckTaskBodyStmt(s, auto_vars, rule, diag);
  }
}

// §23.9: an identifier shall be used to declare only one item within a scope.
// Flags a second variable declaration that reuses a name already declared by a
// prior variable declaration in the SAME scope. Only the declarations that are
// direct members of one block are compared here.
// §23.9 lists "Tasks", "Functions" and "begin-end blocks (named or unnamed)"
// among the elements that define a new scope, which is every construct this is
// called on. §3.13(f) reaches the same result in two steps, introducing a block
// name space for named or unnamed blocks and for the function and task
// constructs, and then forbidding a redeclaration of a name already declared
// within a name space. §23.9 is cited instead because it names the constructs
// and states the prohibition on declarations in one place, and because
// CheckOneBlockLocals in src/elaborator/elaborator_scope_rules.cpp reports the
// same clash in a procedural block under §23.9.
static void CheckBlockDeclDups(const std::vector<Stmt*>& block_stmts,
                               DiagEngine& diag) {
  std::unordered_set<std::string_view> names;
  for (const auto* child : block_stmts) {
    if (!child || child->kind != StmtKind::kVarDecl || child->var_name.empty())
      continue;
    if (!names.insert(child->var_name).second) {
      diag.Error(child->range.start,
                 std::format("redeclaration of '{}'", child->var_name),
                 Subclause("23.9"));
    }
  }
}

// §23.9: functions, tasks and every named or unnamed begin-end or fork-join
// block nested inside the body each define a new scope, and an identifier shall
// be used to declare only one item within a scope. Walks the body so each
// nested block is compared against itself; a name reused in a nested or sibling
// block is a distinct scope, hence legal shadowing rather than a
// redeclaration. The body's own top-level statement list is handled separately
// by the caller (it is a bare statement list, not a kBlock node).
static void CheckSubroutineBodyRedeclarations(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlock) CheckBlockDeclDups(s->stmts, diag);
  // §23.9 lists "fork-join blocks (named or unnamed)" among the elements that
  // define a new scope, beside "begin-end blocks (named or unnamed)". A
  // declaration written directly inside a fork standing in a function or task
  // body lands in Stmt::fork_stmts on a node whose kind is StmtKind::kFork, so
  // that list is the fork-join block's own scope and two declarations of one
  // name in it are a redeclaration. The list is checked on its own rather than
  // merged into the enclosing block's, because the fork-join block is a
  // separate scope and a name reused there is legal shadowing.
  if (s->kind == StmtKind::kFork) CheckBlockDeclDups(s->fork_stmts, diag);
  // §23.9 puts no condition on where the block whose declarations it governs is
  // written, so every position a statement holds a statement in is a position a
  // begin-end or fork-join block stands in. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckSubroutineBodyRedeclarations(sub, diag);
  });
}

void Elaborator::ValidateFunctionBody(const ModuleItem* item) {
  ValidateRefLifetime(item, diag_);

  ValidateConstRefWriteProtection(item, diag_);

  ValidateFunctionArgDecls(item, typedefs_, class_names_, diag_);

  ValidateRefArgsInForkBlocks(item, diag_);

  // §23.9: a function or a task defines a new scope, and an identifier shall be
  // used to declare only one item within a scope, so the body's top-level
  // variable declarations must be unique. Nested begin-end blocks are checked
  // as their own separate scopes during the walk below.
  CheckBlockDeclDups(item->func_body_stmts, diag_);
  for (auto* s : item->func_body_stmts)
    CheckSubroutineBodyRedeclarations(s, diag_);

  if (item->kind == ModuleItemKind::kTaskDecl) {
    ValidateTaskBody(item, diag_);
    return;
  }
  if (item->kind != ModuleItemKind::kFunctionDecl) return;
  bool is_void = (item->return_type.kind == DataTypeKind::kVoid);
  for (auto* s : item->func_body_stmts) {
    CheckFuncBodyStmt(s, is_void, task_names_, item->name, diag_);
  }
}

namespace {

void CollectIdentLeaves(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      if (!e->text.empty() && e->text.front() != '$') out.push_back(e);
      return;
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
      for (auto* a : e->args) CollectIdentLeaves(a, out);
      return;
    case ExprKind::kMemberAccess:
      CollectIdentLeaves(e->lhs, out);
      return;
    case ExprKind::kTypeRef:
      return;
    default:
      break;
  }
  CollectIdentLeaves(e->lhs, out);
  CollectIdentLeaves(e->rhs, out);
  CollectIdentLeaves(e->base, out);
  CollectIdentLeaves(e->index, out);
  CollectIdentLeaves(e->index_end, out);
  CollectIdentLeaves(e->condition, out);
  CollectIdentLeaves(e->true_expr, out);
  CollectIdentLeaves(e->false_expr, out);
  CollectIdentLeaves(e->repeat_count, out);
  CollectIdentLeaves(e->with_expr, out);
  for (auto* a : e->args) CollectIdentLeaves(a, out);
  for (auto* el : e->elements) CollectIdentLeaves(el, out);
}

// Reports each identifier leaf of a default-value expression that is neither a
// previously declared argument nor visible in the subroutine's declaring scope.
template <typename InModuleScopeFn>
void CheckOneArgDefaultScope(
    const FunctionArg& arg,
    const std::unordered_set<std::string_view>& prior_args,
    const InModuleScopeFn& in_module_scope, DiagEngine& diag) {
  std::vector<const Expr*> idents;
  CollectIdentLeaves(arg.default_value, idents);
  for (const auto* e : idents) {
    auto name = e->text;
    if (name.empty()) continue;
    if (prior_args.count(name)) continue;
    if (in_module_scope(name)) continue;
    diag.Error(e->range.start,
               std::format("default value for '{}' references '{}' "
                           "which is not declared in the subroutine's "
                           "declaring scope",
                           arg.name, name),
               Subclause("13.5.3"));
  }
}

}  // namespace

void Elaborator::ValidateFunctionArgDefaultsScope(const ModuleItem* item) {
  if (!item) return;
  if (!item->is_ansi_ports) return;
  if (!item->method_class.empty()) return;
  auto in_module_scope = [this](std::string_view name) {
    return IsNameInModuleScope(name);
  };
  std::unordered_set<std::string_view> prior_args;
  for (const auto& arg : item->func_args) {
    if (arg.default_value) {
      CheckOneArgDefaultScope(arg, prior_args, in_module_scope, diag_);
    }
    if (!arg.name.empty()) prior_args.insert(arg.name);
  }
}

static void CheckAutoVarWritesInProc(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kNonblockingAssign && s->lhs &&
      s->lhs->kind == ExprKind::kIdentifier &&
      auto_vars.count(s->lhs->text) != 0) {
    diag.Error(s->range.start, "automatic variable in nonblocking assignment",
               Subclause("6.21"));
  }
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(s->range.start,
                 "automatic block variable in procedural continuous assignment",
                 Subclause("6.21"));
    }
  }
  // §6.21 forbids the nonblocking assignment and the procedural continuous
  // assignment reported above by what each writes into rather than by where it
  // is written, so every position a statement holds a statement in is one
  // either can stand in. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
  //
  // Stmt::for_inits and Stmt::for_steps are walked because the shared list is
  // walked whole, and no conforming source makes either report: A.6.8 admits
  // only a list_of_variable_assignments or a for_variable_declaration in a
  // for_initialization, and only an operator_assignment, an
  // inc_or_dec_expression or a function_subroutine_call in a for_step, and none
  // of those is a nonblocking assignment, a procedural continuous assignment or
  // a force.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckAutoVarWritesInProc(sub, auto_vars, diag);
  });
}

void Elaborator::ValidateAutomaticVarProcWrites(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (!is_proc || !item->body) continue;
    std::unordered_set<std::string_view> auto_vars;
    CollectAutoVarNames(item->body, false, auto_vars);
    if (auto_vars.empty()) continue;
    CheckAutoVarWritesInProc(item->body, auto_vars, diag_);
  }
}

}  // namespace delta
