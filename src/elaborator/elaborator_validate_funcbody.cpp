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

// §9.3.2: "A return statement within the context of a fork-join block is
// illegal and shall result in a compilation error." The clause puts no
// condition on where inside the fork the return stands, so every position a
// statement holds a statement in is one the rule reaches. ForEachChildStmt in
// elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
//
// Stmt::for_inits and Stmt::for_steps are walked because the shared list is
// walked whole, and no conforming source puts a return in either: A.6.8 admits
// only a list_of_variable_assignments or a for_variable_declaration in a
// for_initialization, and only an operator_assignment, an inc_or_dec_expression
// or a function_subroutine_call in a for_step, and a jump_statement is none of
// those.
//
// `in_production_code_block` is §18.17.6's term. It is set at a randsequence
// statement and stays set below one, through a fork-join written inside a
// production code block as well: a return there aborts the production rather
// than the enclosing subroutine, so the return §9.3.2 forbids is not what is
// written there, however many process boundaries stand between.
static void CheckNoReturnInFork(const Stmt* s, bool in_production_code_block,
                                DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    // §18.17.6: "The return statement aborts the generation of the current
    // production." A return in a randsequence production code block is
    // therefore not the enclosing subroutine's return, and §9.3.2 is about the
    // subroutine's return, so this clause has nothing to report about it.
    if (!in_production_code_block) {
      diag.Error(s->range.start,
                 "return statement is not allowed inside a fork-join block",
                 Subclause("9.3.2"));
    }
    return;
  }
  // Stmt::rs_productions is the only member of Stmt a randsequence statement
  // fills, and every statement it holds stands in one of the two rs_code_blocks
  // A.6.12's rs_rule admits, so the term is set at the randsequence itself.
  bool in_production =
      in_production_code_block || s->kind == StmtKind::kRandsequence;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckNoReturnInFork(sub, in_production, diag);
  });
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

// What §13.4 and §13.4.1 need to know about the function whose body is being
// walked, and §18.17.6 about where in that body the statement being walked
// stands.
struct FunctionBodyScope {
  // §13.4.1: "Functions can be declared as type void, which do not have a
  // return value", so a return carrying one in such a function breaks the
  // clause.
  bool is_void = false;
  // §13.4.1: "It shall also be illegal to declare another object with the same
  // name as the function inside the function scope." A declaration written in
  // the body is compared against this name.
  std::string_view func_name;
  // §13.4: "A function shall not enable tasks regardless of whether those
  // tasks contain time-controlling statements." A call is a task enable when
  // it names one of these.
  const std::unordered_set<std::string_view>& task_names;
  // §18.17.6: "The return statement aborts the generation of the current
  // production." Such a return is not the function's return, and §18.17.7 has
  // it carry an expression -- "A value is returned from a production by using
  // the return with an expression" -- which is the shape §13.4.1's void-return
  // report fires on. The term is what withholds that report.
  bool in_production_code_block = false;
};

static void CheckFuncBodyStmtSelf(const Stmt* s, const FunctionBodyScope& scope,
                                  DiagEngine& diag) {
  // §18.17.6 and §18.17.7: the expression a return carries in a randsequence
  // production code block is the production's value and not a value returned
  // from the function, so §13.4.1's rule about a void function is not what
  // governs it.
  if (s->kind == StmtKind::kReturn && s->expr && scope.is_void &&
      !scope.in_production_code_block) {
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
      scope.task_names.count(s->expr->callee) != 0) {
    diag.Error(s->range.start, "function cannot enable a task",
               Subclause("13.4"));
  }

  CheckFuncBodyVarDecl(s, scope.func_name, diag);

  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts)
      CheckNoReturnInFork(sub, scope.in_production_code_block, diag);
  }
}

// §13.4 and §13.4.1 state the rules a function body is held to and put no
// condition on where in the body the statement breaking one stands, so every
// position a statement holds a statement in is one they reach. ForEachChildStmt
// in elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
//
// Stmt::for_inits is walked because the shared list is walked whole, and no
// conforming source makes any report above from it: A.6.8 admits only a
// list_of_variable_assignments or a for_variable_declaration there, and
// ParserStmtHelpers::ParseForLocalDeclInits in src/parser/parser_stmt.cpp
// leaves a control variable declared local to the loop as an assignment with
// its type in Stmt::for_init_types rather than as a StmtKind::kVarDecl.
// Stmt::for_steps does make one: A.6.8 admits a function_subroutine_call there,
// and a task enable is one.
static void CheckFuncBodyStmt(const Stmt* s, const FunctionBodyScope& scope,
                              DiagEngine& diag) {
  if (!s) return;
  CheckFuncBodyStmtSelf(s, scope, diag);

  // §13.4.4: "Within a function, a fork-join_none construct may contain any
  // statements that are legal within a task", which is the exception §13.4
  // refers to when it opens "with exceptions noted in 13.4.4". The statements
  // under such a fork are answerable to §13.3 rather than to §13.4, so the walk
  // stops here.
  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone)
    return;

  FunctionBodyScope inner = scope;
  // Stmt::rs_productions is the only member of Stmt a randsequence statement
  // fills, and every statement it holds stands in one of the two rs_code_blocks
  // A.6.12's rs_rule admits, so §18.17.6's term is set at the randsequence
  // itself.
  if (s->kind == StmtKind::kRandsequence) inner.in_production_code_block = true;
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckFuncBodyStmt(sub, inner, diag); });
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

// What §13.3 and the clause AutoVarRule selects need to know about the task
// whose body is being walked, and §18.17.6 about where in that body the
// statement being walked stands.
struct TaskBodyScope {
  // The variables the four uses are forbidden of: §13.3.2's "variables declared
  // in automatic tasks", or §6.21's automatic variables where a static task
  // declared them, as CollectAutoVarNames collects them.
  const std::unordered_set<std::string_view>& auto_vars;
  // Which of those two clauses forbids the use, and how its report names the
  // variable. See AutoVarRule above.
  const AutoVarRule& rule;
  // §18.17.6: "The return statement aborts the generation of the current
  // production." Such a return is not the task's return, and §18.17.7 has it
  // carry an expression -- "A value is returned from a production by using the
  // return with an expression" -- which is the shape §13.3's report fires on.
  // The term is what withholds that report.
  bool in_production_code_block = false;
};

static void CheckTaskBodyStmtSelf(const Stmt* s, const TaskBodyScope& scope,
                                  DiagEngine& diag) {
  // §18.17.6 and §18.17.7: the expression a return carries in a randsequence
  // production code block is the production's value and not a value returned
  // from the task, so §13.3's "A task exits when the endtask is reached. The
  // return statement can be used to exit the task before the endtask keyword"
  // is not what governs it.
  if (s->kind == StmtKind::kReturn && s->expr &&
      !scope.in_production_code_block) {
    diag.Error(s->range.start, "task returns a value", Subclause("13.3"));
  }

  CheckTaskBodyNbaForAutoVar(s, scope.auto_vars, scope.rule, diag);
  CheckTaskBodyMonitorTrace(s, scope.auto_vars, scope.rule, diag);
  CheckTaskBodyContAssign(s, scope.auto_vars, scope.rule, diag);

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts)
      CheckNoReturnInFork(sub, scope.in_production_code_block, diag);
  }
}

// §13.3, §13.3.2, §6.21 and §10.6.1 each state a rule about a statement written
// in a task body and put no condition on where in the body it stands, so every
// position a statement holds a statement in is one they reach. ForEachChildStmt
// in elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
//
// Stmt::for_inits is walked because the shared list is walked whole, and no
// conforming source makes any report above from it: A.6.8 admits only a
// list_of_variable_assignments or a for_variable_declaration there, and neither
// is a return, a nonblocking assignment, a procedural continuous assignment or
// a system task call. Stmt::for_steps does make one: A.6.8 admits a
// function_subroutine_call there, and $monitor is one.
static void CheckTaskBodyStmt(const Stmt* s, const TaskBodyScope& scope,
                              DiagEngine& diag) {
  if (!s) return;
  CheckTaskBodyStmtSelf(s, scope, diag);
  TaskBodyScope inner = scope;
  // Stmt::rs_productions is the only member of Stmt a randsequence statement
  // fills, and every statement it holds stands in one of the two rs_code_blocks
  // A.6.12's rs_rule admits, so §18.17.6's term is set at the randsequence
  // itself.
  if (s->kind == StmtKind::kRandsequence) inner.in_production_code_block = true;
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckTaskBodyStmt(sub, inner, diag); });
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
  TaskBodyScope scope{.auto_vars = auto_vars, .rule = rule};
  for (auto* s : item->func_body_stmts) {
    CheckTaskBodyStmt(s, scope, diag);
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
  FunctionBodyScope scope{
      .is_void = is_void, .func_name = item->name, .task_names = task_names_};
  for (auto* s : item->func_body_stmts) {
    CheckFuncBodyStmt(s, scope, diag_);
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
