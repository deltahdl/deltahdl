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

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/system_function_types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static std::optional<ConstVal> ConstEvalSysCallFull(const Expr* expr,
                                                    const ScopeMap& scope) {
  if (expr->callee == "$signed" || expr->callee == "$unsigned") {
    if (expr->args.empty()) return std::nullopt;
    auto arg = ConstEvalFull(expr->args[0], scope);
    if (!arg) return std::nullopt;
    return CastConstVal(*arg, arg->width, expr->callee == "$signed");
  }
  if (expr->callee == "$typename") return ConstEvalStringLiteral(expr);
  auto val = EvalConstSysCall(expr, scope);
  if (!val) return std::nullopt;
  auto listed = std::ranges::find(kSystemFunctionTypes, expr->callee,
                                  &SystemFunctionType::name);
  if (listed == kSystemFunctionTypes.end()) return ConstVal{*val, 32, true};
  return NormalizeConstVal(*val, listed->type.width, listed->type.is_signed);
}

static const RtlirModule* g_param_range_module = nullptr;

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
    if (!ParamVisibleFromScopes(pd.gen_block_prefix, RegisteredGenPrefixes()))
      continue;
    if (!pd.has_decl_range_bounds) return std::nullopt;
    return PackedRange{pd.decl_range_left, pd.decl_range_right};
  }
  return std::nullopt;
}

std::optional<std::string> ScopedNameKey(const Expr* expr) {
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind != ExprKind::kMemberAccess) return std::nullopt;
  auto base = ScopedNameKey(expr->lhs);
  if (!base) return std::nullopt;
  return *base + "." + std::string(expr->rhs->text);
}

static std::optional<ConstVal> ConstEvalMemberAccessFull(
    const Expr* expr, const ScopeMap& scope) {
  if (SpecializationArg arg = ConstEvalSpecializedClassParam(expr, scope);
      arg.supplied)
    return arg.value;
  if (auto builtin = ConstEvalBuiltinMethodFull(expr, scope)) return builtin;
  if (auto part = ConstEvalAggregatePart(expr, scope)) return part;
  if (auto key = ScopedNameKey(expr)) {
    auto it = scope.find(*key);
    if (it == scope.end()) return std::nullopt;
    return ConstVal{FindTwoStateReading(scope, *key).value_or(it->second), 32,
                    true};
  }
  return std::nullopt;
}

static const std::unordered_map<std::string_view, const ModuleItem*>*
    g_const_func_registry = nullptr;

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

static DiagEngine* g_severity_diag = nullptr;
static Arena* g_severity_arena = nullptr;

ConstFuncSeverityGuard::ConstFuncSeverityGuard(DiagEngine& diag, Arena& arena)
    : prev_diag_(g_severity_diag), prev_arena_(g_severity_arena) {
  g_severity_diag = &diag;
  g_severity_arena = &arena;
}

ConstFuncSeverityGuard::~ConstFuncSeverityGuard() {
  g_severity_diag = prev_diag_;
  g_severity_arena = prev_arena_;
}

static DelayMode g_delay_mode = DelayMode::kTyp;

DelayModeGuard::DelayModeGuard(DelayMode mode) : prev_(g_delay_mode) {
  g_delay_mode = mode;
}

DelayModeGuard::~DelayModeGuard() { g_delay_mode = prev_; }

DelayMode ActiveDelayMode() { return g_delay_mode; }

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

static std::optional<int64_t> RoundConstReal(double value) {
  if (!std::isfinite(value)) return std::nullopt;
  return std::llround(value);
}

static std::optional<int64_t> FoldIntegral(const Expr* e,
                                           const ScopeMap& scope) {
  if (auto rounded = FoldRealValueAsInteger(e, scope)) return rounded;
  auto v = ConstEvalFull(e, scope);
  if (!v) return std::nullopt;
  return v->value;
}

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

static std::optional<bool> ConstFuncLoopCond(const Expr* cond,
                                             const ScopeMap& locals) {
  if (!cond) return true;
  return ConstFuncTruth(cond, locals);
}

enum class ConstFuncLoopStep : std::uint8_t { kIterate, kStop, kPropagate };

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

static void BindLoopVarType(std::string_view name, const DataType& type) {
  if (IsConstFuncRealType(type)) {
    SetConstFuncRealLocal(name, 0.0);
  } else {
    ClearConstFuncRealLocal(name);
  }
}

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

static bool IsElabSeverityTask(std::string_view name) {
  return name == "$fatal" || name == "$error" || name == "$warning" ||
         name == "$info";
}

static void ExecConstFuncSystemTask(const Expr* call, const ScopeMap& locals) {
  if (g_severity_diag == nullptr || !IsElabSeverityTask(call->callee)) return;
  ReportConstFuncSeverity(call, locals, *g_severity_diag, *g_severity_arena);
}

static ConstFuncFlow ExecConstFuncExprStmt(const Stmt* s, ScopeMap& locals) {
  const Expr* e = s->expr;
  if (!e) return ConstFuncFlow::kNormal;
  if (e->kind == ExprKind::kSystemCall) {
    ExecConstFuncSystemTask(e, locals);
    return ConstFuncFlow::kNormal;
  }
  bool is_unary =
      e->kind == ExprKind::kPostfixUnary || e->kind == ExprKind::kUnary;
  bool is_step =
      e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus;
  if (is_unary && is_step && e->lhs && e->lhs->kind == ExprKind::kIdentifier) {
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

static bool RunConstFuncBody(const ModuleItem* func, ScopeMap& locals) {
  int64_t iter_budget = kMaxConstFuncIterations;
  for (auto* s : func->func_body_stmts) {
    ConstFuncFlow flow = ExecConstFuncStmt(s, locals, func->name, iter_budget);
    if (flow == ConstFuncFlow::kAbort) return false;
    if (flow == ConstFuncFlow::kReturn) break;
  }
  return true;
}

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
  if (auto param = RegisteredParamValue(expr->text, it->second)) return param;
  return ConstVal{FindTwoStateReading(scope, expr->text).value_or(it->second),
                  32, true};
}

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
      return ConstEvalFull(SelectMinTypMaxMember(expr), scope, ctx);
    case ExprKind::kCall: {
      if (auto builtin = ConstEvalBuiltinMethodFull(expr, scope))
        return builtin;
      if (auto let = ConstEvalLetCall(expr, scope, ctx)) return let;
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
