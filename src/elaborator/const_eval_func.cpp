#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static std::optional<ConstVal> ConstEvalSysCallFull(const Expr* expr,
                                                    const ScopeMap& scope) {
  // §11.7: `$signed` and `$unsigned` evaluate the input expression and return a
  // one-dimensional packed array of its width and value, with the signedness
  // the function names. The width carries over unchanged and only the
  // signedness is set, so the number that width and signedness now make of the
  // operand's bits is what the call is worth: `$unsigned(-4'sd4)` is the four
  // bits 1100 read unsigned, which is 12, and `$signed(4'b1100)` is those same
  // bits read signed, which is -4.
  if (expr->callee == "$signed" || expr->callee == "$unsigned") {
    if (expr->args.empty()) return std::nullopt;
    auto arg = ConstEvalFull(expr->args[0], scope);
    if (!arg) return std::nullopt;
    return CastConstVal(*arg, arg->width, expr->callee == "$signed");
  }
  // §20.6.1: $typename answers a string, and §11.10 makes a string the packed
  // number of its characters, as it makes a string literal.
  if (expr->callee == "$typename") return ConstEvalStringLiteral(expr);
  auto val = EvalConstSysCall(expr, scope);
  if (!val) return std::nullopt;
  return ConstVal{*val, 32, true};
}

// §11.5.1: the module whose parameter declarations the folder may consult for
// the range they were declared with, installed by the elaborator via
// ParamRangeRegistryGuard. Null unless a guard is live.
static const RtlirModule* g_param_range_module = nullptr;

// §23.9: the generate block prefixes in force where the expression being folded
// stands, outermost first. Installed by RegisteredGenScopeGuard and cleared
// whenever a module is installed, because a module is entered at its own level
// and an expression among its own items stands in no generate block.
static std::vector<std::string_view> g_param_range_prefixes;

ParamRangeRegistryGuard::ParamRangeRegistryGuard(const RtlirModule* mod)
    : prev_(g_param_range_module),
      prev_scopes_(std::move(g_param_range_prefixes)) {
  g_param_range_module = mod;
  g_param_range_prefixes.clear();
}

ParamRangeRegistryGuard::~ParamRangeRegistryGuard() {
  g_param_range_module = prev_;
  g_param_range_prefixes = std::move(prev_scopes_);
}

RegisteredGenScopeGuard::RegisteredGenScopeGuard(
    const std::vector<std::string_view>& scopes)
    : prev_(std::move(g_param_range_prefixes)) {
  g_param_range_prefixes = scopes;
}

RegisteredGenScopeGuard::~RegisteredGenScopeGuard() {
  g_param_range_prefixes = std::move(prev_);
}

const RtlirModule* RegisteredModule() { return g_param_range_module; }

const std::vector<std::string_view>& RegisteredGenPrefixes() {
  return g_param_range_prefixes;
}

std::optional<PackedRange> RegisteredParamRange(std::string_view name) {
  if (!g_param_range_module) return std::nullopt;
  for (const auto& pd : g_param_range_module->params) {
    if (pd.name != name) continue;
    // §23.9 puts a parameter a generate block declares in a scope of its own,
    // so a select written outside that block is not addressing it however the
    // names agree. RegisteredGenPrefixes() is where the select stands.
    if (!ParamVisibleFromScopes(pd.gen_block_prefix, RegisteredGenPrefixes()))
      continue;
    if (!pd.has_decl_range_bounds) return std::nullopt;
    return PackedRange{pd.decl_range_left, pd.decl_range_right};
  }
  return std::nullopt;
}

static std::optional<ConstVal> ConstEvalMemberAccessFull(
    const Expr* expr, const ScopeMap& scope) {
  // §8.25.1 makes the override the value of `C#(args)::name`, so an override
  // that was written decides the answer whether or not it folded. Only an
  // absent one falls through to the class default below.
  if (SpecializationArg arg = ConstEvalSpecializedClassParam(expr, scope);
      arg.supplied)
    return arg.value;
  // §5.13 makes the empty parentheses optional, so `c.num` parses as a member
  // access rather than a call and is folded here as well as from the kCall arm
  // of ConstEvalFull.
  if (auto builtin = ConstEvalBuiltinMethodFull(expr, scope)) return builtin;
  if (expr->lhs && expr->rhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->rhs->kind == ExprKind::kIdentifier) {
    std::string compound =
        std::string(expr->lhs->text) + "." + std::string(expr->rhs->text);
    auto it = scope.find(compound);
    if (it != scope.end()) return ConstVal{it->second, 32, true};
  }
  return std::nullopt;
}

// §13.4.3 constant-function-call evaluation ---------------------------------
//
// A constant function is a normal function evaluated at elaboration time so
// that e.g. `localparam addr_width = clogb2(ram_depth)` folds to an integer.
// The registry below is the set of user function declarations visible to the
// design element whose parameters are currently being resolved; it is null
// unless a ConstFuncRegistryGuard is live.
static const std::unordered_map<std::string_view, const ModuleItem*>*
    g_const_func_registry = nullptr;

// Bounds against pathological or (mutually) recursive constant functions:
// depth caps recursion, and each active call carries an iteration budget for
// its loops. Exhausting either simply abandons the fold (returns nullopt),
// leaving the parameter unresolved exactly as before this feature existed —
// never an error and never a wrong value.
static constexpr int kMaxConstFuncDepth = 64;
static constexpr int64_t kMaxConstFuncIterations = 10'000'000;
static int g_const_func_depth = 0;

ConstFuncRegistryGuard::ConstFuncRegistryGuard(
    const std::unordered_map<std::string_view, const ModuleItem*>* funcs)
    : prev_(g_const_func_registry) {
  g_const_func_registry = funcs;
}

ConstFuncRegistryGuard::~ConstFuncRegistryGuard() {
  g_const_func_registry = prev_;
}

const std::unordered_map<std::string_view, const ModuleItem*>*
RegisteredConstFuncs() {
  return g_const_func_registry;
}

// §11.11: the min:typ:max member the folder selects. It is the typical value
// unless a DelayModeGuard installed another, which is what src/main.cpp does
// for the whole of an elaboration.
static const ConstFuncSeverityHandler* g_severity_handler = nullptr;

ConstFuncSeverityGuard::ConstFuncSeverityGuard(ConstFuncSeverityHandler handler)
    : handler_(std::move(handler)), prev_(g_severity_handler) {
  g_severity_handler = &handler_;
}

ConstFuncSeverityGuard::~ConstFuncSeverityGuard() {
  g_severity_handler = prev_;
}

static DelayMode g_delay_mode = DelayMode::kTyp;

DelayModeGuard::DelayModeGuard(DelayMode mode) : prev_(g_delay_mode) {
  g_delay_mode = mode;
}

DelayModeGuard::~DelayModeGuard() { g_delay_mode = prev_; }

DelayMode ActiveDelayMode() { return g_delay_mode; }

// Control-flow outcome of interpreting one constant-function statement.
enum class ConstFuncFlow : std::uint8_t {
  kNormal,
  kReturn,
  kBreak,
  kContinue,
  kAbort
};

static ConstFuncFlow ExecConstFuncStmt(const Stmt* s, ScopeMap& locals,
                                       std::string_view result_name,
                                       int64_t& iter_budget);

// §6.12.1: the integer a real converts to, rounded with a half away from zero;
// none for a value that is no number.
static std::optional<int64_t> RoundConstReal(double value) {
  if (!std::isfinite(value)) return std::nullopt;
  return std::llround(value);
}

// The integer `e` folds to against `scope`: a real expression rounded
// (HasRealOperand, §6.12.1), and any other folded as an integer.
static std::optional<int64_t> FoldIntegral(const Expr* e,
                                           const ScopeMap& scope) {
  if (auto rounded = FoldRealValueAsInteger(e, scope)) return rounded;
  auto v = ConstEvalFull(e, scope);
  if (!v) return std::nullopt;
  return v->value;
}

// Stores the value of `rhs` into the local `name`, as an assignment converts
// it (§6.12.1): a real local (ConstFuncRealFrame) takes the real `rhs` is, an
// integral one the value rounded where `rhs` is real (HasRealOperand) and the
// integer it folds to otherwise. False where `rhs` does not fold.
static bool StoreConstFuncLocal(std::string_view name, const Expr* rhs,
                                ScopeMap& locals) {
  if (ConstFuncRealLocal(name)) {
    auto real = ConstEvalReal(rhs, locals);
    if (!real) return false;
    SetConstFuncRealLocal(name, *real);
    locals[name] = RoundConstReal(*real).value_or(0);
    return true;
  }
  auto v = FoldIntegral(rhs, locals);
  if (!v) return false;
  locals[name] = *v;
  return true;
}

// A constant function may only assign to a simple (unindexed) local — its
// arguments, body-declared variables, or the implicit result variable named
// after the function. Anything else abandons the fold.
static bool ConstFuncAssign(const Expr* lhs, const Expr* rhs,
                            ScopeMap& locals) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier || lhs->text.empty())
    return false;
  return StoreConstFuncLocal(lhs->text, rhs, locals);
}

static ConstFuncFlow ExecConstFuncStmts(const std::vector<Stmt*>& stmts,
                                        ScopeMap& locals,
                                        std::string_view result_name,
                                        int64_t& iter_budget) {
  for (auto* s : stmts) {
    ConstFuncFlow flow = ExecConstFuncStmt(s, locals, result_name, iter_budget);
    if (flow != ConstFuncFlow::kNormal) return flow;
  }
  return ConstFuncFlow::kNormal;
}

// §13.4.3: body-local variables initialize as they would for normal
// simulation. Model that as a fresh binding, seeded from the initializer when
// one is present and 0 otherwise; one declared real is a real local
// (ConstFuncRealFrame) starting at 0.0 (§6.8, Table 6-7).
static ConstFuncFlow ExecConstFuncVarDecl(const Stmt* s, ScopeMap& locals) {
  if (s->var_name.empty()) return ConstFuncFlow::kNormal;
  locals[s->var_name] = 0;
  if (IsConstFuncRealType(s->var_decl_type))
    SetConstFuncRealLocal(s->var_name, 0.0);
  if (s->var_init && !StoreConstFuncLocal(s->var_name, s->var_init, locals))
    return ConstFuncFlow::kAbort;
  return ConstFuncFlow::kNormal;
}

static ConstFuncFlow ExecConstFuncBlockingAssign(const Stmt* s,
                                                 ScopeMap& locals) {
  if (!s->rhs) return ConstFuncFlow::kAbort;
  if (!ConstFuncAssign(s->lhs, s->rhs, locals)) return ConstFuncFlow::kAbort;
  return ConstFuncFlow::kNormal;
}

std::optional<bool> ConstFuncTruth(const Expr* cond, const ScopeMap& scope) {
  if (HasRealOperand(cond)) {
    auto real = ConstEvalReal(cond, scope);
    if (!real) return std::nullopt;
    return *real != 0.0;
  }
  auto v = ConstEvalFull(cond, scope);
  if (!v) return std::nullopt;
  return ConstValIsNonZero(*v);
}

static ConstFuncFlow ExecConstFuncIf(const Stmt* s, ScopeMap& locals,
                                     std::string_view result_name,
                                     int64_t& iter_budget) {
  auto cond = ConstFuncTruth(s->condition, locals);
  if (!cond) return ConstFuncFlow::kAbort;
  if (*cond)
    return ExecConstFuncStmt(s->then_branch, locals, result_name, iter_budget);
  return ExecConstFuncStmt(s->else_branch, locals, result_name, iter_budget);
}

// Fold a loop's continuation condition. An absent expression is the always-true
// condition of `for (;;)`; nullopt means the expression did not fold, which
// abandons the enclosing loop.
static std::optional<bool> ConstFuncLoopCond(const Expr* cond,
                                             const ScopeMap& locals) {
  if (!cond) return true;
  return ConstFuncTruth(cond, locals);
}

// What one pass over a loop body asks the enclosing loop to do next.
enum class ConstFuncLoopStep : std::uint8_t {
  kIterate,   // run the next iteration
  kStop,      // the body broke out of the loop
  kPropagate  // the body returned or abandoned the fold; `out` carries which
};

// Run one iteration of a loop body, charging it against the shared iteration
// budget so a loop whose condition never folds false cannot hang elaboration.
static ConstFuncLoopStep ExecConstFuncLoopBody(const Stmt* body,
                                               ScopeMap& locals,
                                               std::string_view result_name,
                                               int64_t& iter_budget,
                                               ConstFuncFlow& out) {
  if (--iter_budget < 0) {
    out = ConstFuncFlow::kAbort;
    return ConstFuncLoopStep::kPropagate;
  }
  ConstFuncFlow flow =
      ExecConstFuncStmt(body, locals, result_name, iter_budget);
  if (flow == ConstFuncFlow::kReturn || flow == ConstFuncFlow::kAbort) {
    out = flow;
    return ConstFuncLoopStep::kPropagate;
  }
  if (flow == ConstFuncFlow::kBreak) return ConstFuncLoopStep::kStop;
  return ConstFuncLoopStep::kIterate;
}

static ConstFuncFlow ExecConstFuncForLoop(const Stmt* s, ScopeMap& locals,
                                          std::string_view result_name,
                                          int64_t& iter_budget) {
  if (ExecConstFuncStmts(s->for_inits, locals, result_name, iter_budget) ==
      ConstFuncFlow::kAbort)
    return ConstFuncFlow::kAbort;
  while (true) {
    auto go = ConstFuncLoopCond(s->for_cond, locals);
    if (!go) return ConstFuncFlow::kAbort;
    if (!*go) break;
    ConstFuncFlow out = ConstFuncFlow::kNormal;
    ConstFuncLoopStep step = ExecConstFuncLoopBody(
        s->for_body, locals, result_name, iter_budget, out);
    if (step == ConstFuncLoopStep::kPropagate) return out;
    if (step == ConstFuncLoopStep::kStop) break;
    if (ExecConstFuncStmts(s->for_steps, locals, result_name, iter_budget) ==
        ConstFuncFlow::kAbort)
      return ConstFuncFlow::kAbort;
  }
  return ConstFuncFlow::kNormal;
}

// §12.7.1: a for loop that declares its control variables stands in an
// implicit begin-end block, so each declared variable hides any local of the
// same name for the loop's duration and the local is as it was once the loop
// ends. A loop that returns or abandons the fold leaves nothing to restore.
// §12.7.1 with §6.12: a loop variable declared real is a real local for the
// loop's run, and one of any other type no real local whatever the name was
// outside the loop (ConstFuncRealFrame).
static void BindLoopVarType(std::string_view name, const DataType& type) {
  if (IsConstFuncRealType(type)) {
    SetConstFuncRealLocal(name, 0.0);
  } else {
    ClearConstFuncRealLocal(name);
  }
}

// The real binding `real` the name `name` had outside a loop, handed back.
static void RestoreRealBinding(std::string_view name,
                               std::optional<double> real) {
  if (real) {
    SetConstFuncRealLocal(name, *real);
  } else {
    ClearConstFuncRealLocal(name);
  }
}

static ConstFuncFlow ExecConstFuncFor(const Stmt* s, ScopeMap& locals,
                                      std::string_view result_name,
                                      int64_t& iter_budget) {
  std::vector<std::pair<std::string_view, int64_t>> hidden;
  std::vector<std::pair<std::string_view, std::optional<double>>> reals;
  for (size_t i = 0; i < s->for_init_types.size(); ++i) {
    if (s->for_init_types[i].kind == DataTypeKind::kImplicit) continue;
    std::string_view name = s->for_inits[i]->lhs->text;
    auto outer = locals.find(name);
    if (outer != locals.end()) hidden.emplace_back(*outer);
    reals.emplace_back(name, ConstFuncRealLocal(name));
    BindLoopVarType(name, s->for_init_types[i]);
  }
  ConstFuncFlow flow =
      ExecConstFuncForLoop(s, locals, result_name, iter_budget);
  if (flow != ConstFuncFlow::kNormal) return flow;
  for (const auto& [name, value] : hidden) locals[name] = value;
  for (const auto& [name, real] : reals) RestoreRealBinding(name, real);
  return flow;
}

static ConstFuncFlow ExecConstFuncWhile(const Stmt* s, ScopeMap& locals,
                                        std::string_view result_name,
                                        int64_t& iter_budget) {
  while (true) {
    auto go = ConstFuncLoopCond(s->condition, locals);
    if (!go) return ConstFuncFlow::kAbort;
    if (!*go) break;
    ConstFuncFlow out = ConstFuncFlow::kNormal;
    ConstFuncLoopStep step =
        ExecConstFuncLoopBody(s->body, locals, result_name, iter_budget, out);
    if (step == ConstFuncLoopStep::kPropagate) return out;
    if (step == ConstFuncLoopStep::kStop) break;
  }
  return ConstFuncFlow::kNormal;
}

static ConstFuncFlow ExecConstFuncDoWhile(const Stmt* s, ScopeMap& locals,
                                          std::string_view result_name,
                                          int64_t& iter_budget) {
  while (true) {
    ConstFuncFlow out = ConstFuncFlow::kNormal;
    ConstFuncLoopStep step =
        ExecConstFuncLoopBody(s->body, locals, result_name, iter_budget, out);
    if (step == ConstFuncLoopStep::kPropagate) return out;
    if (step == ConstFuncLoopStep::kStop) break;
    auto go = ConstFuncLoopCond(s->condition, locals);
    if (!go) return ConstFuncFlow::kAbort;
    if (!*go) break;
  }
  return ConstFuncFlow::kNormal;
}

static ConstFuncFlow ExecConstFuncRepeat(const Stmt* s, ScopeMap& locals,
                                         std::string_view result_name,
                                         int64_t& iter_budget) {
  auto count = ConstEvalFull(s->condition, locals);
  if (!count) return ConstFuncFlow::kAbort;
  for (int64_t i = 0; i < count->value; ++i) {
    ConstFuncFlow out = ConstFuncFlow::kNormal;
    ConstFuncLoopStep step =
        ExecConstFuncLoopBody(s->body, locals, result_name, iter_budget, out);
    if (step == ConstFuncLoopStep::kPropagate) return out;
    if (step == ConstFuncLoopStep::kStop) break;
  }
  return ConstFuncFlow::kNormal;
}

static ConstFuncFlow ExecConstFuncReturn(const Stmt* s, ScopeMap& locals,
                                         std::string_view result_name) {
  if (s->expr && !StoreConstFuncLocal(result_name, s->expr, locals))
    return ConstFuncFlow::kAbort;
  return ConstFuncFlow::kReturn;
}

// §20.10.1: whether `name` is one of the elaboration severity tasks.
static bool IsElabSeverityTask(std::string_view name) {
  return name == "$fatal" || name == "$error" || name == "$warning" ||
         name == "$info";
}

// §13.4.3: system task calls in a constant function are ignored but for the
// elaboration severity tasks of §20.10.1, handed to the live
// ConstFuncSeverityGuard's handler. Other bare
// expression statements — a pre/post increment on a local, say — are
// interpreted for their side effect; anything else abandons the fold.
static ConstFuncFlow ExecConstFuncExprStmt(const Stmt* s, ScopeMap& locals) {
  const Expr* e = s->expr;
  if (!e) return ConstFuncFlow::kNormal;
  if (e->kind == ExprKind::kSystemCall) {
    if (g_severity_handler != nullptr && IsElabSeverityTask(e->callee))
      (*g_severity_handler)(e, locals);
    return ConstFuncFlow::kNormal;
  }
  bool is_unary =
      e->kind == ExprKind::kPostfixUnary || e->kind == ExprKind::kUnary;
  bool is_step =
      e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus;
  if (is_unary && is_step && e->lhs && e->lhs->kind == ExprKind::kIdentifier) {
    // §11.4.2: `++` and `--` on a real add and subtract 1.0.
    if (auto real = ConstFuncRealLocal(e->lhs->text)) {
      double next = e->op == TokenKind::kPlusPlus ? *real + 1.0 : *real - 1.0;
      SetConstFuncRealLocal(e->lhs->text, next);
      locals[e->lhs->text] = RoundConstReal(next).value_or(0);
      return ConstFuncFlow::kNormal;
    }
    auto cur = ConstEvalFull(e->lhs, locals);
    if (!cur) return ConstFuncFlow::kAbort;
    locals[e->lhs->text] =
        e->op == TokenKind::kPlusPlus ? cur->value + 1 : cur->value - 1;
    return ConstFuncFlow::kNormal;
  }
  return ConstFuncFlow::kAbort;
}

// §13.4.3 excludes no case statement from a constant function: the arm it
// selects (ConstFuncCaseArm) runs as the statement would.
static ConstFuncFlow ExecConstFuncCase(const Stmt* s, ScopeMap& locals,
                                       std::string_view result_name,
                                       int64_t& iter_budget) {
  std::optional<const Stmt*> arm = ConstFuncCaseArm(s, locals);
  if (!arm) return ConstFuncFlow::kAbort;
  return ExecConstFuncStmt(*arm, locals, result_name, iter_budget);
}

static ConstFuncFlow ExecConstFuncStmt(const Stmt* s, ScopeMap& locals,
                                       std::string_view result_name,
                                       int64_t& iter_budget) {
  if (!s) return ConstFuncFlow::kNormal;
  switch (s->kind) {
    case StmtKind::kNull:
      return ConstFuncFlow::kNormal;
    case StmtKind::kBlock:
      return ExecConstFuncStmts(s->stmts, locals, result_name, iter_budget);
    case StmtKind::kVarDecl:
    case StmtKind::kBlockItemDecl:
      return ExecConstFuncVarDecl(s, locals);
    case StmtKind::kBlockingAssign:
      return ExecConstFuncBlockingAssign(s, locals);
    case StmtKind::kIf:
      return ExecConstFuncIf(s, locals, result_name, iter_budget);
    case StmtKind::kCase:
      return ExecConstFuncCase(s, locals, result_name, iter_budget);
    case StmtKind::kFor:
      return ExecConstFuncFor(s, locals, result_name, iter_budget);
    case StmtKind::kWhile:
      return ExecConstFuncWhile(s, locals, result_name, iter_budget);
    case StmtKind::kDoWhile:
      return ExecConstFuncDoWhile(s, locals, result_name, iter_budget);
    case StmtKind::kRepeat:
      return ExecConstFuncRepeat(s, locals, result_name, iter_budget);
    case StmtKind::kReturn:
      return ExecConstFuncReturn(s, locals, result_name);
    case StmtKind::kBreak:
      return ConstFuncFlow::kBreak;
    case StmtKind::kContinue:
      return ConstFuncFlow::kContinue;
    case StmtKind::kExprStmt:
      return ExecConstFuncExprStmt(s, locals);
    default:
      return ConstFuncFlow::kAbort;
  }
}

// §13.4.3: fold a call to a user-defined constant function. Returns nullopt
// (leaving the surrounding constant expression unresolved) whenever the callee
// is not a registered user function, an argument is not itself constant, or the
// body uses a construct the elaboration-time interpreter does not model.
// Bind each formal argument to the constant value of the matching actual,
// falling back to the formal's default when the call supplies fewer actuals.
// False means some actual did not fold, which abandons the whole call.
// A formal declared real takes the real its actual is (§6.12), held in
// `reals` until the callee's frame (ConstFuncRealFrame) exists, as the actual
// is evaluated in the caller's.
using RealBindings = std::vector<std::pair<std::string_view, double>>;

static bool BindConstFuncArg(const FunctionArg& fa, const Expr* arg_expr,
                             const ScopeMap& scope, ScopeMap& locals,
                             RealBindings& reals) {
  if (IsConstFuncRealType(fa.data_type)) {
    auto real = ConstEvalReal(arg_expr, scope);
    if (!real) return false;
    reals.emplace_back(fa.name, *real);
    locals[fa.name] = RoundConstReal(*real).value_or(0);
    return true;
  }
  auto v = FoldIntegral(arg_expr, scope);
  if (!v) return false;
  locals[fa.name] = *v;
  return true;
}

static bool BindConstFuncArgs(const ModuleItem* func, const Expr* expr,
                              const ScopeMap& scope, ScopeMap& locals,
                              RealBindings& reals) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const FunctionArg& fa = func->func_args[i];
    const Expr* arg_expr =
        i < expr->args.size() ? expr->args[i] : fa.default_value;
    if (!arg_expr) return false;
    if (!BindConstFuncArg(fa, arg_expr, scope, locals, reals)) return false;
  }
  return true;
}

// Interpret the body statements in order, stopping at the first `return`.
// False means the body used a construct the interpreter does not model or ran
// out of its iteration budget.
static bool RunConstFuncBody(const ModuleItem* func, ScopeMap& locals) {
  int64_t iter_budget = kMaxConstFuncIterations;
  for (auto* s : func->func_body_stmts) {
    ConstFuncFlow flow = ExecConstFuncStmt(s, locals, func->name, iter_budget);
    if (flow == ConstFuncFlow::kAbort) return false;
    if (flow == ConstFuncFlow::kReturn) break;
  }
  return true;
}

// §26.3: the key a call is registered under -- the bare callee, or for a
// call written through the package scope resolution operator, `pk::f(...)`,
// which the parser keeps as a call with no callee text and the scoped name as
// its base, the "pk::f" the package's functions are registered under.
static std::string ConstCallKey(const Expr* expr) {
  if (!expr->callee.empty()) return std::string(expr->callee);
  const Expr* scoped = expr->lhs;
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution || scoped->lhs == nullptr ||
      scoped->lhs->kind != ExprKind::kIdentifier || scoped->rhs == nullptr ||
      scoped->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return std::string(scoped->lhs->text) + "::" + std::string(scoped->rhs->text);
}

const ModuleItem* RegisteredConstFunc(const Expr* call) {
  if (!g_const_func_registry) return nullptr;
  std::string key = ConstCallKey(call);
  if (key.empty()) return nullptr;
  auto it = g_const_func_registry->find(key);
  if (it == g_const_func_registry->end() || it->second == nullptr ||
      it->second->kind != ModuleItemKind::kFunctionDecl)
    return nullptr;
  return it->second;
}

// What a constant function call returns: the integer its result variable
// holds, and the real it holds where the function returns a real (§6.12).
struct ConstCallResult {
  int64_t value;
  std::optional<double> real;
};

static std::optional<ConstCallResult> RunConstFuncCall(const Expr* expr,
                                                       const ScopeMap& scope) {
  const ModuleItem* func = RegisteredConstFunc(expr);
  if (func == nullptr) return std::nullopt;
  if (g_const_func_depth >= kMaxConstFuncDepth) return std::nullopt;
  ++g_const_func_depth;
  struct DepthGuard {
    ~DepthGuard() { --g_const_func_depth; }
  } depth_guard;

  // The body sees the caller's parameter scope (a constant function may
  // reference module/package/$unit parameters, §13.4.3), overlaid with the
  // argument bindings and the implicit result variable.
  ScopeMap locals = scope;
  RealBindings reals;
  if (!BindConstFuncArgs(func, expr, scope, locals, reals)) return std::nullopt;
  ConstFuncRealFrame frame;
  for (const auto& [name, value] : reals) SetConstFuncRealLocal(name, value);
  if (!func->name.empty()) {
    locals[func->name] = 0;
    if (IsConstFuncRealType(func->return_type))
      SetConstFuncRealLocal(func->name, 0.0);
  }
  if (!RunConstFuncBody(func, locals)) return std::nullopt;
  auto rit = locals.find(func->name);
  if (rit == locals.end()) return std::nullopt;
  return ConstCallResult{rit->second, ConstFuncRealLocal(func->name)};
}

// §6.12.1: a real result read as an integer is rounded.
static std::optional<ConstVal> ConstEvalUserCall(const Expr* expr,
                                                 const ScopeMap& scope) {
  auto result = RunConstFuncCall(expr, scope);
  if (!result) return std::nullopt;
  if (!result->real) return ConstVal{result->value, 32, true};
  auto rounded = RoundConstReal(*result->real);
  if (!rounded) return std::nullopt;
  return ConstVal{*rounded, 32, true};
}

std::optional<double> ConstEvalUserCallReal(const Expr* call,
                                            const ScopeMap& scope) {
  auto result = RunConstFuncCall(call, scope);
  if (!result) return std::nullopt;
  return result->real.value_or(static_cast<double>(result->value));
}

// §3.12.1: a $unit:: prefix forces resolution to the compilation-unit scope,
// bypassing any same-named local that would otherwise shadow it. Those values
// are aliased under a "$unit::"-qualified key by BuildParamScope, so a match
// there is the outermost declaration and a miss must not silently fall back to
// the shadowing local.
static std::optional<ConstVal> ConstEvalIdentifierFull(const Expr* expr,
                                                       const ScopeMap& scope) {
  if (expr->scope_prefix == "$unit") {
    std::string key = "$unit::";
    key += expr->text;
    auto uit = scope.find(key);
    if (uit != scope.end()) return ConstVal{uit->second, 32, true};
    return std::nullopt;
  }
  auto it = scope.find(expr->text);
  if (it == scope.end()) return std::nullopt;
  // §6.20.2: a name standing for a parameter of the registered module has the
  // parameter's declared width and signedness; any other name -- a constant
  // function's local, a package or class constant under its qualified key --
  // is read as the 32-bit signed integer it always was.
  if (auto param = RegisteredParamValue(expr->text, it->second)) return param;
  return ConstVal{it->second, 32, true};
}

// §11.11 orders the three values minimum, then typical, then maximum, which
// Parser::ParseMinTypMaxExpr in src/parser/expr_parser_patterns.cpp and
// Parser::ParseParenExpr in src/parser/expr_parser_aux.cpp both record as
// Expr::lhs, Expr::condition and Expr::rhs in that order.
const Expr* SelectMinTypMaxMember(const Expr* expr) {
  switch (ActiveDelayMode()) {
    case DelayMode::kMin:
      return expr->lhs;
    case DelayMode::kMax:
      return expr->rhs;
    case DelayMode::kTyp:
      break;
  }
  return expr->condition;
}

// The value of `expr` itself, before ReadInContext converts it to `ctx`. The
// operator expressions and the conditional hand the context down to their
// context-determined operands, and an unbased unsized literal is as wide as
// the context (§5.7.1); every other form is self-determined in itself, and
// its parts are.
static std::optional<ConstVal> ConstEvalNode(const Expr* expr,
                                             const ScopeMap& scope,
                                             FoldContext ctx) {
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return ConstEvalLiteral(expr);
    case ExprKind::kUnbasedUnsizedLiteral:
      return ConstEvalUnbasedUnsized(expr, ctx);
    case ExprKind::kStringLiteral:
      return ConstEvalStringLiteral(expr);
    case ExprKind::kIdentifier:
      return ConstEvalIdentifierFull(expr, scope);
    case ExprKind::kUnary:
      return ConstEvalUnaryFull(expr, scope, ctx);
    case ExprKind::kBinary:
      return ConstEvalBinaryFull(expr, scope, ctx);
    case ExprKind::kTernary:
      return ConstEvalTernaryFull(expr, scope, ctx);
    case ExprKind::kConcatenation:
      return ConstEvalConcatFull(expr, scope);
    case ExprKind::kReplicate:
      return ConstEvalReplicateFull(expr, scope);
    case ExprKind::kSelect:
      return ConstEvalSelectFull(expr, scope);
    case ExprKind::kSystemCall:
      return ConstEvalSysCallFull(expr, scope);
    case ExprKind::kCast:
      return ConstEvalCastFull(expr, scope);
    case ExprKind::kMemberAccess:
      return ConstEvalMemberAccessFull(expr, scope);
    case ExprKind::kMinTypMax:
      // §11.11 admits three colon-separated expressions anywhere an expression
      // may stand, for the minimum, typical and maximum values in that order,
      // so a constant expression can be written as one. Which of the three
      // folds is what ActiveDelayMode answers, and EvalMinTypMax in
      // src/simulator/evaluation.cpp selects by that same setting, so a
      // parameter folded at elaboration and a delay waited out during the run
      // cannot disagree. The member stands where the form stands, so the
      // context reaches it.
      return ConstEvalFull(SelectMinTypMaxMember(expr), scope, ctx);
    case ExprKind::kCall: {
      // §11.2.1: a constant built-in method call (§5.13) is evaluated at
      // elaboration time. It is tried first because a built-in method is not a
      // user function and would never be found in the §13.4.3 registry below.
      if (auto builtin = ConstEvalBuiltinMethodFull(expr, scope))
        return builtin;
      // §13.4.3: a call to a user-defined constant function folds at
      // elaboration time.
      return ConstEvalUserCall(expr, scope);
    }
    default:
      return std::nullopt;
  }
}

std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope,
                                      FoldContext ctx) {
  if (!expr) return std::nullopt;
  auto value = ConstEvalNode(expr, scope, ctx);
  if (!value) return std::nullopt;
  // §11.8.2 (printed page 303): an operand the propagation reaches is
  // converted to the propagated size and type, extended from its sign only
  // where that type is signed.
  return ReadInContext(*value, ctx);
}

std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope) {
  return ConstEvalFull(expr, scope, FoldContext{});
}

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope) {
  auto result = ConstEvalFull(expr, scope);
  if (!result) return std::nullopt;
  return result->value;
}

std::optional<int64_t> ConstEvalInt(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalInt(expr, kEmptyScope);
}

struct StaticPrefixResult {
  std::string text;
  bool is_static;
};

// How a folded index is spelled: as the integer it is, which the §9.2.2
// checks compare, or by its 32 bits, the name the simulator holds an element
// under (ArrayElementKey in src/simulator/lowerer_var.cpp), so `p[-1]` of
// `p [-1:0]` is "p[4294967295]".
enum class PrefixIndexSpelling : uint8_t { kValue, kStorage };

struct StaticPrefixSpec {
  const ScopeMap& scope;
  PrefixIndexSpelling spelling;
};

static StaticPrefixResult BuildStaticPrefix(const Expr* expr,
                                            const StaticPrefixSpec& spec);

static StaticPrefixResult BuildIdentifierPrefix(const Expr* expr) {
  std::string result;
  if (!expr->scope_prefix.empty()) result += expr->scope_prefix;
  result += expr->text;
  return {result, true};
}

static StaticPrefixResult BuildMemberAccessPrefix(
    const Expr* expr, const StaticPrefixSpec& spec) {
  if (!expr->lhs || !expr->rhs) return {"", false};
  auto base = BuildStaticPrefix(expr->lhs, spec);
  if (!base.is_static) return {base.text, false};
  return {base.text + "." + std::string(expr->rhs->text), true};
}

static StaticPrefixResult BuildSelectPrefix(const Expr* expr,
                                            const StaticPrefixSpec& spec) {
  auto base = BuildStaticPrefix(expr->base, spec);
  if (base.text.empty()) return {"", false};
  if (!base.is_static) return {base.text, false};
  auto idx = ConstEvalInt(expr->index, spec.scope);
  if (!idx) return {base.text, false};
  // §11.5.3: a part-select whose bounds are constant stays in the prefix
  // whole, spelled with the addresses it covers, lower first -- `v[4:7]` for
  // `v[7:4]` and `v[4 -: 4]` alike -- so that two prefixes of one base are
  // compared by the bits they reach and not by their first address alone.
  if (spec.spelling == PrefixIndexSpelling::kValue && expr->index_end) {
    auto end = ConstEvalInt(expr->index_end, spec.scope);
    if (!end) return {base.text, false};
    int64_t last = *end;
    if (expr->is_part_select_plus) last = *idx + *end - 1;
    if (expr->is_part_select_minus) last = *idx - *end + 1;
    return {base.text + "[" + std::to_string(std::min(*idx, last)) + ":" +
                std::to_string(std::max(*idx, last)) + "]",
            true};
  }
  std::string index = spec.spelling == PrefixIndexSpelling::kStorage
                          ? std::to_string(static_cast<uint32_t>(*idx))
                          : std::to_string(*idx);
  return {base.text + "[" + index + "]", true};
}

static StaticPrefixResult BuildStaticPrefix(const Expr* expr,
                                            const StaticPrefixSpec& spec) {
  if (!expr) return {"", false};

  if (expr->kind == ExprKind::kIdentifier) {
    return BuildIdentifierPrefix(expr);
  }

  if (expr->kind == ExprKind::kMemberAccess) {
    return BuildMemberAccessPrefix(expr, spec);
  }

  if (expr->kind == ExprKind::kSelect && expr->base) {
    return BuildSelectPrefix(expr, spec);
  }

  return {"", false};
}

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return "";
  return BuildStaticPrefix(expr, {scope, PrefixIndexSpelling::kValue}).text;
}

std::string LongestStaticStorageName(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return BuildStaticPrefix(expr, {kEmptyScope, PrefixIndexSpelling::kStorage})
      .text;
}

}  // namespace delta
