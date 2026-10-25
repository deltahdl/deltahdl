#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/system_functions.h"
#include "elaborator/class_member_names.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsValidOutputArg(const Expr* e) {
  if (!e) return false;
  // §13.5: an output/inout actual is restricted to an expression that is valid
  // on the left-hand side of a procedural assignment (§10.4). A concatenation
  // is such an lvalue only when every element is itself a valid lvalue, so a
  // concatenation containing a non-assignable element (e.g. a literal) is
  // rejected just like a bare literal actual would be.
  // §10.8 (printed page 260) counts the actual of an output or inout argument
  // among the assignment-like contexts, so §10.9 lets a positional pattern of
  // lvalues stand there as the side being assigned.
  if (e->kind == ExprKind::kConcatenation ||
      (e->kind == ExprKind::kAssignmentPattern && e->pattern_keys.empty())) {
    if (e->elements.empty()) return false;
    for (const auto* el : e->elements) {
      if (!IsValidOutputArg(el)) return false;
    }
    return true;
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

static bool IsArgProvided(const Expr* expr, size_t i, std::string_view name,
                          size_t positional_count) {
  if (expr->arg_names.empty())
    return (i < expr->args.size()) && (expr->args[i] != nullptr);
  if (i < positional_count) return (expr->args[i] != nullptr);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == name) return true;
  }
  return false;
}

static void CheckRequiredArgs(const Expr* expr, const ModuleItem* func,
                              size_t positional_count, DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    bool provided =
        IsArgProvided(expr, i, func->func_args[i].name, positional_count);
    if (!provided && !func->func_args[i].default_value) {
      diag.Error(expr->range.start,
                 std::format("missing argument '{}' in call to '{}'",
                             func->func_args[i].name, func->name),
                 Subclause("13.5.3"));
    }
  }
}

static void CheckNamedArgs(const Expr* expr, const ModuleItem* func,
                           DiagEngine& diag) {
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    bool found = false;
    for (size_t i = 0; i < func->func_args.size(); ++i) {
      if (func->func_args[i].name == expr->arg_names[j]) {
        found = true;
        break;
      }
    }
    if (!found) {
      diag.Error(expr->range.start,
                 std::format("no parameter '{}' in '{}'", expr->arg_names[j],
                             func->name),
                 Subclause("13.5.4"));
    }
  }
}

static int ResolveCallArgIndex(const Expr* expr, size_t i,
                               std::string_view name, size_t positional_count) {
  if (expr->arg_names.empty()) {
    return (i < expr->args.size()) ? static_cast<int>(i) : -1;
  }
  if (i < positional_count) return static_cast<int>(i);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

static std::string_view RefActualNetName(
    const Expr* e, const std::unordered_set<std::string_view>& nets);

// §13.5 with §10.4: the net an output or inout actual names -- whole, through
// a select, or as an element of a concatenation or positional pattern -- or
// empty for none.
static std::string_view OutputActualNetName(
    const Expr* e, const std::unordered_set<std::string_view>& nets) {
  if (e->kind != ExprKind::kConcatenation &&
      e->kind != ExprKind::kAssignmentPattern)
    return RefActualNetName(e, nets);
  for (const Expr* el : e->elements) {
    std::string_view net = OutputActualNetName(el, nets);
    if (!net.empty()) return net;
  }
  return {};
}

static void CheckOutputArgs(const Expr* expr, const ModuleItem* func,
                            size_t positional_count,
                            const std::unordered_set<std::string_view>& nets,
                            DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    int ai =
        ResolveCallArgIndex(expr, i, func->func_args[i].name, positional_count);
    if (ai < 0) continue;
    auto* arg = expr->args[static_cast<size_t>(ai)];
    if (arg == nullptr) continue;
    std::string_view kind = dir == Direction::kOutput ? "output" : "inout";
    if (!IsValidOutputArg(arg)) {
      diag.Error(arg->range.start,
                 std::format("{} argument '{}' requires a variable", kind,
                             func->func_args[i].name),
                 Subclause("13.5"));
      continue;
    }
    std::string_view net = OutputActualNetName(arg, nets);
    if (net.empty()) continue;
    diag.Error(arg->range.start,
               std::format("net '{}' cannot be the actual of {} argument '{}'",
                           net, kind, func->func_args[i].name),
               Subclause("13.5"));
  }
}

static std::string_view RefActualNetName(
    const Expr* e, const std::unordered_set<std::string_view>& nets) {
  if (!e || nets.empty()) return {};
  if (e->kind == ExprKind::kIdentifier) {
    return nets.count(e->text) ? e->text : std::string_view{};
  }
  if (e->kind == ExprKind::kSelect) {
    return RefActualNetName(e->base, nets);
  }
  return {};
}

// §13.5.2: a ref argument refers to a variable, so its actual names one --
// whole, through a select or as a member -- and §10.8 excludes passing to a ref
// argument from the assignment-like contexts, which leaves an untyped pattern
// there no type to take. A net is no variable either.
static void CheckRefArgs(const Expr* expr, const ModuleItem* func,
                         size_t positional_count,
                         const std::unordered_set<std::string_view>& net_names,
                         DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    if (func->func_args[i].direction != Direction::kRef) continue;
    int ai =
        ResolveCallArgIndex(expr, i, func->func_args[i].name, positional_count);
    if (ai < 0) continue;
    auto* arg = expr->args[static_cast<size_t>(ai)];
    if (arg == nullptr) continue;
    if (arg->kind != ExprKind::kIdentifier && arg->kind != ExprKind::kSelect &&
        arg->kind != ExprKind::kMemberAccess) {
      diag.Error(arg->range.start,
                 std::format("ref argument '{}' of '{}' requires a variable",
                             func->func_args[i].name, func->name),
                 Subclause("13.5.2"));
      continue;
    }
    auto net = RefActualNetName(arg, net_names);
    if (net.empty()) continue;
    diag.Error(arg->range.start,
               std::format("net '{}' cannot be passed by reference to "
                           "argument '{}' of '{}'",
                           net, func->func_args[i].name, func->name),
               Subclause("13.5.2"));
  }
}

static void CheckCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return;
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  size_t param_count = func->func_args.size();
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  if (positional_count > param_count) {
    diag.Error(expr->range.start,
               std::format("too many arguments to '{}': expected {}, got {}",
                           func->name, param_count, positional_count),
               Subclause("13.5"));
    return;
  }
  CheckRequiredArgs(expr, func, positional_count, diag);
  CheckNamedArgs(expr, func, diag);
  CheckOutputArgs(expr, func, positional_count, net_names, diag);
  CheckRefArgs(expr, func, positional_count, net_names, diag);
}

static void CheckVoidCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    // §35.5.5 lets an imported function declare `void` for its result, and
    // §35.5 makes its usage that of a native function, so §13.4.1's rule about
    // a void function used as an operand reaches an import as well. An
    // imported task is excluded here rather than by its result type, which
    // §35.5.4 leaves unwritten for one.
    if (it != func_decls.end() &&
        (it->second->kind == ModuleItemKind::kFunctionDecl ||
         (it->second->kind == ModuleItemKind::kDpiImport &&
          !it->second->dpi_is_task)) &&
        it->second->return_type.kind == DataTypeKind::kVoid) {
      diag.Error(expr->range.start,
                 std::format("void function '{}' used as expression operand",
                             expr->callee),
                 Subclause("13.4.1"));
    }
  }
  CheckVoidCallInExpr(expr->lhs, func_decls, diag);
  CheckVoidCallInExpr(expr->rhs, func_decls, diag);
  CheckVoidCallInExpr(expr->condition, func_decls, diag);
  CheckVoidCallInExpr(expr->true_expr, func_decls, diag);
  CheckVoidCallInExpr(expr->false_expr, func_decls, diag);
  for (auto* a : expr->args) CheckVoidCallInExpr(a, func_decls, diag);
  for (auto* e : expr->elements) CheckVoidCallInExpr(e, func_decls, diag);
}

static std::string_view ForbiddenFuncArgInNonProc(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return {};
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return {};
  const auto* func = it->second;
  if (func->kind != ModuleItemKind::kFunctionDecl) return {};
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kOutput) return "output";
    if (arg.direction == Direction::kInout) return "inout";

    if (arg.direction == Direction::kRef && !arg.is_const) return "ref";
  }
  return {};
}

static void CheckNoTaskCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = decls.find(expr->callee);
    if (it != decls.end() && it->second->kind == ModuleItemKind::kTaskDecl) {
      diag.Error(expr->range.start,
                 std::format("task '{}' cannot be called in an event "
                             "expression",
                             expr->callee),
                 Subclause("9.4.2"));
    }
  }
  CheckNoTaskCallInExpr(expr->lhs, decls, diag);
  CheckNoTaskCallInExpr(expr->rhs, decls, diag);
  CheckNoTaskCallInExpr(expr->condition, decls, diag);
  CheckNoTaskCallInExpr(expr->true_expr, decls, diag);
  CheckNoTaskCallInExpr(expr->false_expr, decls, diag);
  CheckNoTaskCallInExpr(expr->base, decls, diag);
  CheckNoTaskCallInExpr(expr->index, decls, diag);
  CheckNoTaskCallInExpr(expr->index_end, decls, diag);
  for (auto* a : expr->args) CheckNoTaskCallInExpr(a, decls, diag);
  for (auto* e : expr->elements) CheckNoTaskCallInExpr(e, decls, diag);
}

static void CheckEventExprSingular(
    const Expr* expr,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier && !expr->text.empty()) {
    if (non_singular_vars.count(expr->text) != 0) {
      diag.Error(
          expr->range.start,
          std::format(
              "event expression references non-singular "
              "variable '{}'; an event can only be watched on a singular value",
              expr->text),
          Subclause("9.4.2"));
    }
  }
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    if (non_singular_funcs.count(expr->callee) != 0) {
      diag.Error(expr->range.start,
                 std::format("event expression calls function '{}' whose "
                             "return type is non-singular; an event can only "
                             "be watched on a singular value",
                             expr->callee),
                 Subclause("9.4.2"));
    }
  }
  // §9.4.2: an aggregate may appear in an event expression as long as the
  // expression reduces to a singular value. A member select such as `s.a`
  // yields a singular result, so the aggregate object on the left of the `.`
  // need not itself be singular — do not flag it. (Element selects like
  // `arr[0]` carry their operand in the base/index fields, which are already
  // not walked here.)
  if (expr->kind != ExprKind::kMemberAccess) {
    CheckEventExprSingular(expr->lhs, non_singular_vars, non_singular_funcs,
                           diag);
  }
  CheckEventExprSingular(expr->rhs, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->condition, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->true_expr, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->false_expr, non_singular_vars,
                         non_singular_funcs, diag);
  for (auto* a : expr->args)
    CheckEventExprSingular(a, non_singular_vars, non_singular_funcs, diag);
  for (auto* e : expr->elements)
    CheckEventExprSingular(e, non_singular_vars, non_singular_funcs, diag);
}

// §9.4.2 holds every event expression to a singular value and puts no
// condition on where the statement carrying the event control stands; A.6.4
// makes a procedural_timing_control_statement a statement_item, and the
// clause's own example writes three event controls inside a fork-join. Every
// position a statement holds a statement in is therefore one this check is owed
// at, and ForEachChildStmt in elaborator_validate_internal.h states those
// positions once for the whole elaborator. It hands the visitor the field
// itself, so a walk that only reads the tree takes a `Stmt* const&`.
static void WalkStmtForEventSingular(
    const Stmt* s,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (!s) return;
  // An event control's events, and the intra-assignment event control a
  // blocking or nonblocking assignment carries (§9.4.5), `x = @(e) y;`; no
  // other statement holds any.
  for (const auto& ev : s->events) {
    CheckEventExprSingular(ev.signal, non_singular_vars, non_singular_funcs,
                           diag);
    CheckEventExprSingular(ev.iff_condition, non_singular_vars,
                           non_singular_funcs, diag);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtForEventSingular(sub, non_singular_vars, non_singular_funcs, diag);
  });
}

static void CheckCallNoOutInoutRefInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag, std::string_view context) {
  if (!expr) return;
  auto bad = ForbiddenFuncArgInNonProc(expr, func_decls);
  if (!bad.empty()) {
    diag.Error(expr->range.start,
               std::format("function '{}' has {} argument; cannot be called "
                           "in {}",
                           expr->callee, bad, context),
               Subclause("13.4"));
  }
  CheckCallNoOutInoutRefInExpr(expr->lhs, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->rhs, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->condition, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->true_expr, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->false_expr, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->base, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->index, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->index_end, func_decls, diag, context);
  for (auto* a : expr->args)
    CheckCallNoOutInoutRefInExpr(a, func_decls, diag, context);
  for (auto* e : expr->elements)
    CheckCallNoOutInoutRefInExpr(e, func_decls, diag, context);
}

static void WalkExprForCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!expr) return;
  CheckCallArgs(expr, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->lhs, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->rhs, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->condition, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->true_expr, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->false_expr, func_decls, net_names, diag);
  for (auto* a : expr->args)
    WalkExprForCallArgs(a, func_decls, net_names, diag);
  for (auto* e : expr->elements)
    WalkExprForCallArgs(e, func_decls, net_names, diag);
}

// The name a call statement whose expression is `e` calls with its
// parentheses left off, as the walk's map keys it: a name alone or a
// package-scoped name, `p::g`, written as the statement or within its void
// cast (A.6.9). Empty for any other statement.
static std::string ParenOmittedCallName(const Expr* e) {
  if (e->kind == ExprKind::kCast) e = e->lhs;
  if (e->kind == ExprKind::kIdentifier) return std::string(e->text);
  if (e->kind != ExprKind::kMemberAccess || !e->is_scope_resolution) return {};
  return std::format("{}::{}", e->lhs->text, e->rhs->text);
}

// §13.5.5 with A.8.2's footnote 42: a call statement whose expression `e`
// calls the subroutine `name` with its parentheses left off; check that the
// omission is legal here.
static void CheckParenOmittedCall(
    const Expr* e, std::string_view name,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  auto it = func_decls.find(name);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  // §35.5: an imported function is used much as a native SystemVerilog function
  // is, so §13.5.5 decides an imported subroutine's paren-omitted call by what
  // §35.5.4 declared it as. A task is a task by its keyword, and a function is
  // void by the result type §35.5.5 required it to state.
  bool is_import = func->kind == ModuleItemKind::kDpiImport;
  bool is_task = func->kind == ModuleItemKind::kTaskDecl ||
                 (is_import && func->dpi_is_task);
  bool is_void_func = (func->kind == ModuleItemKind::kFunctionDecl ||
                       (is_import && !func->dpi_is_task)) &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (!is_task && !is_void_func) {
    diag.Error(e->range.start,
               std::format("cannot omit parentheses in call to nonvoid "
                           "function '{}'",
                           name),
               Subclause("13.5.5"));
    return;
  }
  // §13.5.5: parentheses may be omitted only when the subroutine has
  // no formal arguments, or when every formal has a default value.
  bool all_have_defaults = true;
  for (const auto& arg : func->func_args) {
    if (!arg.default_value) {
      all_have_defaults = false;
      break;
    }
  }
  if (!all_have_defaults) {
    diag.Error(e->range.start,
               std::format("cannot omit parentheses in call to '{}': "
                           "not all formal arguments have defaults",
                           name),
               Subclause("13.5.5"));
  }
}

// §13.4.1: what a statement calling a nonvoid function may do about the
// result it discards.
constexpr std::string_view kCastToVoid = "cast to void to silence this warning";

bool ReturnsAValue(const ModuleItem* subroutine) {
  // §35.5 makes an imported function's usage that of a native one, so §13.4.1's
  // warning about a discarded result covers a call to one. An imported task is
  // excluded by its keyword: §35.5.4 writes no result type for one, so its
  // result type would otherwise read as a non-void type here.
  return (subroutine->kind == ModuleItemKind::kFunctionDecl ||
          (subroutine->kind == ModuleItemKind::kDpiImport &&
           !subroutine->dpi_is_task)) &&
         subroutine->return_type.kind != DataTypeKind::kVoid;
}

void WarnDiscardedReturn(SourceLoc loc, std::string_view callee,
                         std::string_view remedy, DiagEngine& diag) {
  diag.Warning(loc,
               std::format("return value of nonvoid function '{}' is "
                           "discarded; {}",
                           callee, remedy),
               Subclause("13.4.1"));
}

// §13.4.1: an expression-statement call discards its result; warn if it is a
// nonvoid function (a void'(...) cast wraps the call in a kCast and so does not
// reach this check). Also checks the argument expressions for void operands.
static void CheckDiscardedCallStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  for (auto* a : s->expr->args) CheckVoidCallInExpr(a, func_decls, diag);

  auto fit = func_decls.find(s->expr->callee);
  if (fit == func_decls.end() || !ReturnsAValue(fit->second)) return;
  WarnDiscardedReturn(s->expr->range.start, s->expr->callee, kCastToVoid, diag);
}

// §13.4.1: a statement calling one of the standard's system functions
// discards its result as one calling a nonvoid function does. A statement
// calling $cast, $system or $stacktrace calls the task, which
// IsStandardSystemFunction leaves out.
static void CheckDiscardedSystemCallStmt(const Stmt* s, DiagEngine& diag) {
  if (s->expr == nullptr || s->kind != StmtKind::kExprStmt ||
      s->expr->kind != ExprKind::kSystemCall ||
      !IsStandardSystemFunction(s->expr->callee)) {
    return;
  }
  WarnDiscardedReturn(s->expr->range.start, s->expr->callee, kCastToVoid, diag);
}

// §9.4.2: an event expression cannot call functions with out/inout/ref
// arguments, cannot call tasks, and must yield singular values.
static void CheckEventControlCalls(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  for (const auto& ev : s->events) {
    CheckCallNoOutInoutRefInExpr(ev.signal, func_decls, diag,
                                 "an event expression");
    CheckCallNoOutInoutRefInExpr(ev.iff_condition, func_decls, diag,
                                 "an event expression");

    CheckNoTaskCallInExpr(ev.signal, func_decls, diag);
    CheckNoTaskCallInExpr(ev.iff_condition, func_decls, diag);
  }
}

static void WalkStmtForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag);

// Recurse into every substatement and sub-expression of `s`. A.6.4 makes a
// subroutine_call_statement a statement_item and none of §13.5, §13.5.2,
// §13.5.3, §13.5.4, §13.5.5, §13.4.1, §13.4 or §9.4.2 conditions its rule on
// where the call stands, so every position a statement holds a statement in is
// one these reports are owed at; §13.4.4 settles the fork arms, a fork-join
// inside a function holding any statement legal within a task. ForEachChildStmt
// in elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
static void WalkChildStmtsForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  WalkExprForCallArgs(s->expr, func_decls, net_names, diag);
  WalkExprForCallArgs(s->lhs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->rhs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->condition, func_decls, net_names, diag);
  WalkExprForCallArgs(s->for_cond, func_decls, net_names, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtForCallArgs(sub, func_decls, net_names, diag);
  });
}

static void WalkStmtForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!s) return;

  if (s->kind == StmtKind::kExprStmt && s->expr) {
    const std::string kName = ParenOmittedCallName(s->expr);
    if (!kName.empty()) CheckParenOmittedCall(s->expr, kName, func_decls, diag);
  }

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall) {
    CheckDiscardedCallStmt(s, func_decls, diag);
  } else {
    CheckVoidCallInExpr(s->expr, func_decls, diag);
    CheckDiscardedSystemCallStmt(s, diag);
  }
  CheckVoidCallInExpr(s->rhs, func_decls, diag);
  CheckVoidCallInExpr(s->condition, func_decls, diag);
  CheckVoidCallInExpr(s->for_cond, func_decls, diag);

  if (s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce) {
    CheckCallNoOutInoutRefInExpr(s->rhs, func_decls, diag,
                                 "a procedural continuous assignment");
  }
  // §9.4.2 and §13.4: the events of an event control, and of the
  // intra-assignment event control a blocking or nonblocking assignment
  // carries (§9.4.5), `a = @(f(y)) b;`, are event expressions alike.
  if (!s->events.empty()) CheckEventControlCalls(s, func_decls, diag);
  WalkChildStmtsForCallArgs(s, func_decls, net_names, diag);
}

static std::unordered_map<std::string_view, const ModuleItem*> BuildAllDecls(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
    // §35.5: an imported function is used much as a native SystemVerilog
    // function is, so the §13.5 checks over a call's actuals apply to a
    // subroutine §35.5.4 declared as an import. Its formal list is in the same
    // ModuleItem::func_args field, and each check below reads the declaration's
    // kind where the rule turns on it.
    if (item->kind == ModuleItemKind::kDpiImport) all_decls[item->name] = item;
  }
  return all_decls;
}

// Collects names of variables whose declared type is non-singular (an unpacked
// array or unpacked struct/union).
static std::unordered_set<std::string_view> CollectNonSingularVars(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> non_singular_vars;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    bool unpacked_array = !item->unpacked_dims.empty();
    bool unpacked_aggregate = (item->data_type.kind == DataTypeKind::kStruct ||
                               item->data_type.kind == DataTypeKind::kUnion) &&
                              !item->data_type.is_packed;
    if (unpacked_array || unpacked_aggregate)
      non_singular_vars.insert(item->name);
  }
  return non_singular_vars;
}

// Collects names of functions whose return type is non-singular (an unpacked
// struct/union), drawn from `decl` and the elaborator's known functions.
static std::unordered_set<std::string_view> CollectNonSingularFuncs(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  std::unordered_set<std::string_view> non_singular_funcs;
  auto add_if_non_singular_return = [&](const ModuleItem* item) {
    if (item->kind != ModuleItemKind::kFunctionDecl) return;
    const auto& rt = item->return_type;
    bool unpacked_aggregate =
        (rt.kind == DataTypeKind::kStruct || rt.kind == DataTypeKind::kUnion) &&
        !rt.is_packed;
    if (unpacked_aggregate) non_singular_funcs.insert(item->name);
  };
  for (const auto* item : decl->items) add_if_non_singular_return(item);
  for (const auto& [name, item] : func_decls) add_if_non_singular_return(item);
  return non_singular_funcs;
}

// The set of per-module lookup tables consulted while validating subroutine
// calls and event expressions (§9.4.2, §13.4.x, §13.5.5). These travel together
// as one validation context: the map of callable subroutines, the net names
// (for ref-arg legality), and the sets of non-singular variables/functions
// (for event-expression singular-value checks), plus the diagnostic sink.
struct SubroutineCallContext {
  const std::unordered_map<std::string_view, const ModuleItem*>& all_decls;
  const std::unordered_set<std::string_view>& net_names;
  const std::unordered_set<std::string_view>& non_singular_vars;
  const std::unordered_set<std::string_view>& non_singular_funcs;
  DiagEngine& diag;
  // The classes of the unit, whose members a method's name alone calls first.
  const SoleClassIndex& classes;
};

// Validates one sensitivity-list event expression (the `signal` and
// `iff_condition` of a single entry): call legality, no task calls, and
// singular-value requirements.
static void ValidateSensitivityEntry(const Expr* signal,
                                     const Expr* iff_condition,
                                     const SubroutineCallContext& ctx) {
  CheckCallNoOutInoutRefInExpr(signal, ctx.all_decls, ctx.diag,
                               "an event expression");
  CheckCallNoOutInoutRefInExpr(iff_condition, ctx.all_decls, ctx.diag,
                               "an event expression");

  CheckNoTaskCallInExpr(signal, ctx.all_decls, ctx.diag);
  CheckNoTaskCallInExpr(iff_condition, ctx.all_decls, ctx.diag);

  CheckEventExprSingular(signal, ctx.non_singular_vars, ctx.non_singular_funcs,
                         ctx.diag);
  CheckEventExprSingular(iff_condition, ctx.non_singular_vars,
                         ctx.non_singular_funcs, ctx.diag);
}

// Validates the event expressions in a procedural block's body and sensitivity
// list: call legality, no task calls, and singular-value requirements.
static void ValidateProcBlockEvents(const ModuleItem* item,
                                    const SubroutineCallContext& ctx) {
  WalkStmtForCallArgs(item->body, ctx.all_decls, ctx.net_names, ctx.diag);

  WalkStmtForEventSingular(item->body, ctx.non_singular_vars,
                           ctx.non_singular_funcs, ctx.diag);

  for (const auto& ev : item->sensitivity) {
    ValidateSensitivityEntry(ev.signal, ev.iff_condition, ctx);
  }
}

// Validates the subroutine-call rules in a function or task body.
static void ValidateSubroutineBodyCallArgs(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  for (auto* s : item->func_body_stmts) {
    WalkStmtForCallArgs(s, all_decls, net_names, diag);
  }
}

// Validates the subroutine-call rules in a continuous assignment's RHS.
static void ValidateContAssignCallArgs(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    DiagEngine& diag) {
  CheckVoidCallInExpr(item->assign_rhs, all_decls, diag);

  CheckCallNoOutInoutRefInExpr(item->assign_rhs, all_decls, diag,
                               "a continuous assignment");
}

static void ValidateCallArgsInItem(const ModuleItem* item,
                                   const SubroutineCallContext& ctx);

// The context `ctx` with the subroutines `decls` in place of its own.
static SubroutineCallContext WithDecls(
    const SubroutineCallContext& ctx,
    const std::unordered_map<std::string_view, const ModuleItem*>& decls) {
  return {
      decls,    ctx.net_names, ctx.non_singular_vars, ctx.non_singular_funcs,
      ctx.diag, ctx.classes};
}

// Keys each task and function the items `items` declare in `decls` by its
// name.
static void AddSubroutines(
    const std::vector<ModuleItem*>& items,
    std::unordered_map<std::string_view, const ModuleItem*>& decls) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      decls[item->name] = item;
    }
  }
}

// §27.1 with §23.9: the items `items` of one generate block, walked as the
// module's are, the tasks and functions the block declares callable within it.
static void ValidateCallArgsInBlock(const std::vector<ModuleItem*>& items,
                                    const SubroutineCallContext& ctx) {
  std::unordered_map<std::string_view, const ModuleItem*> decls = ctx.all_decls;
  AddSubroutines(items, decls);
  const SubroutineCallContext kInner = WithDecls(ctx, decls);
  for (const ModuleItem* item : items) ValidateCallArgsInItem(item, kInner);
}

// §27.4 and §27.5: each block of the generate construct `construct`: a loop's
// one block, each block of a conditional construct and of the else chain after
// it, and each case item's block.
static void ValidateCallArgsInGenerate(const ModuleItem& construct,
                                       const SubroutineCallContext& ctx) {
  for (const ModuleItem* branch = &construct; branch != nullptr;
       branch = branch->gen_else) {
    ValidateCallArgsInBlock(branch->gen_body, ctx);
    for (const GenerateCaseItem& item : branch->gen_case_items) {
      ValidateCallArgsInBlock(item.body, ctx);
    }
  }
}

// §8.13: each method body the class `cls` writes, and those of the classes
// nested in it (§8.23), walked with every name the class or a class it extends
// declares taken out of the scope's subroutines. A name alone calls that
// member first, and a method may leave its parentheses off (footnote 42 of
// A.8.2). Where the names are not known in full, a class extending its type
// parameter or a class no scope declares, any name may be a member's, so the
// methods are left alone.
static void ValidateCallArgsInClass(const ClassDecl& cls,
                                    const SubroutineCallContext& ctx) {
  std::unordered_set<std::string_view> members;
  if (!ctx.classes.SelectableNames(cls, members)) return;
  std::unordered_map<std::string_view, const ModuleItem*> decls = ctx.all_decls;
  for (std::string_view name : members) decls.erase(name);
  const SubroutineCallContext kInner = WithDecls(ctx, decls);
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kMethod) {
      ValidateSubroutineBodyCallArgs(member->method, decls, ctx.net_names,
                                     ctx.diag);
    }
    if (member->nested_class != nullptr) {
      ValidateCallArgsInClass(*member->nested_class, kInner);
    }
  }
}

// Validates the subroutine-call rules in one item, a generate construct's
// blocks and a class's methods among them.
static void ValidateCallArgsInItem(const ModuleItem* item,
                                   const SubroutineCallContext& ctx) {
  if (IsProceduralItemKind(item->kind)) {
    ValidateProcBlockEvents(item, ctx);
  }
  if (item->kind == ModuleItemKind::kGenerateIf ||
      item->kind == ModuleItemKind::kGenerateCase ||
      item->kind == ModuleItemKind::kGenerateFor) {
    ValidateCallArgsInGenerate(*item, ctx);
  }
  if (item->kind == ModuleItemKind::kClassDecl) {
    ValidateCallArgsInClass(*item->class_decl, ctx);
  }

  if (item->kind == ModuleItemKind::kFunctionDecl ||
      item->kind == ModuleItemKind::kTaskDecl) {
    ValidateSubroutineBodyCallArgs(item, ctx.all_decls, ctx.net_names,
                                   ctx.diag);
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    ValidateContAssignCallArgs(item, ctx.all_decls, ctx.diag);
  }
  // §13.4: a declaration's initializer stands in no procedural statement.
  CheckCallNoOutInoutRefInExpr(item->init_expr, ctx.all_decls, ctx.diag,
                               "a declaration's initializer");
}

void Elaborator::ValidateSubroutineCallArgs(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      BuildAllDecls(decl, func_decls_);
  // A call scoped by a package, `p::g;`, leaves its parentheses off by the
  // same rule as one by a name alone, so each subroutine of a package is
  // keyed by its scoped name as well.
  for (const PackageDecl* package : unit_->packages) {
    for (const ModuleItem* item : package->items) {
      if (item->kind != ModuleItemKind::kFunctionDecl &&
          item->kind != ModuleItemKind::kTaskDecl) {
        continue;
      }
      const std::string kKey = std::format("{}::{}", package->name, item->name);
      all_decls.emplace(
          std::string_view(arena_.AllocString(kKey.c_str(), kKey.size()),
                           kKey.size()),
          item);
    }
  }

  ValidateScopeRandomizeCalls(decl);

  std::unordered_set<std::string_view> non_singular_vars =
      CollectNonSingularVars(decl);
  std::unordered_set<std::string_view> non_singular_funcs =
      CollectNonSingularFuncs(decl, func_decls_);

  const SoleClassIndex kClasses(*unit_);
  SubroutineCallContext ctx{all_decls,          net_names_, non_singular_vars,
                            non_singular_funcs, diag_,      kClasses};
  for (const auto* item : decl->items) {
    ValidateCallArgsInItem(item, ctx);
  }
}

void ValidateUnitClassCallArgs(const CompilationUnit& unit, DiagEngine& diag) {
  const SoleClassIndex kClasses(unit);
  const std::unordered_set<std::string_view> kNone;
  // A package's classes see its subroutines, and the unit's classes the
  // unit's; a package sees nothing the unit declares (§26.3).
  auto walk_site = [&](const std::vector<ModuleItem*>& items,
                       const std::vector<ClassDecl*>& classes) {
    std::unordered_map<std::string_view, const ModuleItem*> decls;
    AddSubroutines(items, decls);
    const SubroutineCallContext kCtx{decls, kNone, kNone,
                                     kNone, diag,  kClasses};
    for (const ClassDecl* cls : classes) ValidateCallArgsInClass(*cls, kCtx);
    for (const ModuleItem* item : items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ValidateCallArgsInClass(*item->class_decl, kCtx);
      }
    }
  };
  walk_site(unit.cu_items, unit.classes);
  for (const PackageDecl* package : unit.packages)
    walk_site(package->items, {});
}

}  // namespace delta
