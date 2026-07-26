#include <cmath>
#include <cstring>
#include <unordered_set>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

static std::optional<ConstVal> ConstEvalSysCallFull(const Expr* expr,
                                                    const ScopeMap& scope) {
  if (expr->callee == "$signed" || expr->callee == "$unsigned") {
    if (expr->args.empty()) return std::nullopt;
    auto arg = ConstEvalFull(expr->args[0], scope);
    if (!arg) return std::nullopt;
    return ConstVal{arg->value, arg->width, expr->callee == "$signed"};
  }
  auto val = EvalConstSysCall(expr, scope);
  if (!val) return std::nullopt;
  return ConstVal{*val, 32, true};
}

// §8.25.1: registry of parameterized-class declarations visible to the constant
// folder, installed by the elaborator via ParamClassRegistryGuard. Null unless
// a guard is live. Used to map an accessed value-parameter name to its port
// position when resolving a specialization override.
static const std::unordered_map<std::string_view, const ClassDecl*>*
    g_param_class_registry = nullptr;

ParamClassRegistryGuard::ParamClassRegistryGuard(
    const std::unordered_map<std::string_view, const ClassDecl*>* classes)
    : prev_(g_param_class_registry) {
  g_param_class_registry = classes;
}

ParamClassRegistryGuard::~ParamClassRegistryGuard() {
  g_param_class_registry = prev_;
}

// §8.25.1: when a member access is `C#(args)::name` and `name` is one of class
// C's value parameter ports, fold to that specialization's override for `name`
// rather than the class default. Matches a named override (`.name(value)`)
// first, then an ordered override occupying the parameter's port position. Type
// parameters and body-local parameters are not overridable through #(...) and
// are left to the ordinary "Class.name" default lookup.
static std::optional<ConstVal> ConstEvalSpecializationOverride(
    const Expr* expr, const ScopeMap& scope) {
  if (!g_param_class_registry) return std::nullopt;
  const Expr* base = expr->lhs;
  if (!base || base->kind != ExprKind::kIdentifier || !base->has_param_spec ||
      base->elements.empty())
    return std::nullopt;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier)
    return std::nullopt;
  auto cit = g_param_class_registry->find(base->text);
  if (cit == g_param_class_registry->end() || cit->second == nullptr)
    return std::nullopt;
  const ClassDecl* decl = cit->second;
  size_t pos = decl->params.size();
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == expr->rhs->text) {
      pos = i;
      break;
    }
  }
  if (pos == decl->params.size()) return std::nullopt;
  if (decl->type_param_names.count(expr->rhs->text)) return std::nullopt;
  const auto& elems = base->elements;
  const auto& names = base->arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == expr->rhs->text &&
        elems[j]) {
      return ConstEvalFull(elems[j], scope);
    }
  }
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size() && elems[pos]) {
    return ConstEvalFull(elems[pos], scope);
  }
  return std::nullopt;
}

static std::optional<ConstVal> ConstEvalMemberAccessFull(
    const Expr* expr, const ScopeMap& scope) {
  if (auto override_val = ConstEvalSpecializationOverride(expr, scope))
    return override_val;
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

// Control-flow outcome of interpreting one constant-function statement.
enum class ConstFuncFlow { kNormal, kReturn, kBreak, kContinue, kAbort };

static ConstFuncFlow ExecConstFuncStmt(const Stmt* s, ScopeMap& locals,
                                       std::string_view result_name,
                                       int64_t& iter_budget);

// A constant function may only assign to a simple (unindexed) local — its
// arguments, body-declared variables, or the implicit result variable named
// after the function. Anything else abandons the fold.
static bool ConstFuncAssign(const Expr* lhs, int64_t value, ScopeMap& locals) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier || lhs->text.empty())
    return false;
  locals[lhs->text] = value;
  return true;
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
    case StmtKind::kBlockItemDecl: {
      // §13.4.3: body-local variables initialize as they would for normal
      // simulation. Model that as a fresh binding, seeded from the initializer
      // when one is present and 0 otherwise.
      if (s->var_name.empty()) return ConstFuncFlow::kNormal;
      int64_t init = 0;
      if (s->var_init) {
        auto v = ConstEvalFull(s->var_init, locals);
        if (!v) return ConstFuncFlow::kAbort;
        init = v->value;
      }
      locals[s->var_name] = init;
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kBlockingAssign: {
      if (!s->rhs) return ConstFuncFlow::kAbort;
      auto v = ConstEvalFull(s->rhs, locals);
      if (!v) return ConstFuncFlow::kAbort;
      if (!ConstFuncAssign(s->lhs, v->value, locals))
        return ConstFuncFlow::kAbort;
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kIf: {
      auto cond = ConstEvalFull(s->condition, locals);
      if (!cond) return ConstFuncFlow::kAbort;
      if (cond->value)
        return ExecConstFuncStmt(s->then_branch, locals, result_name,
                                 iter_budget);
      return ExecConstFuncStmt(s->else_branch, locals, result_name,
                               iter_budget);
    }
    case StmtKind::kFor: {
      ConstFuncFlow init_flow =
          ExecConstFuncStmts(s->for_inits, locals, result_name, iter_budget);
      if (init_flow == ConstFuncFlow::kAbort) return ConstFuncFlow::kAbort;
      while (true) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        if (s->for_cond) {
          auto cond = ConstEvalFull(s->for_cond, locals);
          if (!cond) return ConstFuncFlow::kAbort;
          if (!cond->value) break;
        }
        ConstFuncFlow body =
            ExecConstFuncStmt(s->for_body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
        ConstFuncFlow step =
            ExecConstFuncStmts(s->for_steps, locals, result_name, iter_budget);
        if (step == ConstFuncFlow::kAbort) return ConstFuncFlow::kAbort;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kWhile: {
      while (true) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        auto cond = ConstEvalFull(s->condition, locals);
        if (!cond) return ConstFuncFlow::kAbort;
        if (!cond->value) break;
        ConstFuncFlow body =
            ExecConstFuncStmt(s->body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kDoWhile: {
      while (true) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        ConstFuncFlow body =
            ExecConstFuncStmt(s->body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
        auto cond = ConstEvalFull(s->condition, locals);
        if (!cond) return ConstFuncFlow::kAbort;
        if (!cond->value) break;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kRepeat: {
      auto count = ConstEvalFull(s->condition, locals);
      if (!count) return ConstFuncFlow::kAbort;
      for (int64_t i = 0; i < count->value; ++i) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        ConstFuncFlow body =
            ExecConstFuncStmt(s->body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kReturn: {
      if (s->expr) {
        auto v = ConstEvalFull(s->expr, locals);
        if (!v) return ConstFuncFlow::kAbort;
        if (!result_name.empty()) locals[result_name] = v->value;
      }
      return ConstFuncFlow::kReturn;
    }
    case StmtKind::kBreak:
      return ConstFuncFlow::kBreak;
    case StmtKind::kContinue:
      return ConstFuncFlow::kContinue;
    case StmtKind::kExprStmt: {
      // §13.4.3: system task calls in a constant function are ignored (the
      // elaboration severity tasks of §20.10.1 are handled elsewhere). Other
      // bare expression statements — a pre/post increment on a local, say — are
      // interpreted for their side effect; anything else abandons the fold.
      const Expr* e = s->expr;
      if (!e) return ConstFuncFlow::kNormal;
      if (e->kind == ExprKind::kSystemCall) return ConstFuncFlow::kNormal;
      if ((e->kind == ExprKind::kPostfixUnary || e->kind == ExprKind::kUnary) &&
          e->lhs && e->lhs->kind == ExprKind::kIdentifier &&
          (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus)) {
        auto cur = ConstEvalFull(e->lhs, locals);
        if (!cur) return ConstFuncFlow::kAbort;
        int64_t nv =
            e->op == TokenKind::kPlusPlus ? cur->value + 1 : cur->value - 1;
        locals[e->lhs->text] = nv;
        return ConstFuncFlow::kNormal;
      }
      return ConstFuncFlow::kAbort;
    }
    default:
      return ConstFuncFlow::kAbort;
  }
}

// §13.4.3: fold a call to a user-defined constant function. Returns nullopt
// (leaving the surrounding constant expression unresolved) whenever the callee
// is not a registered user function, an argument is not itself constant, or the
// body uses a construct the elaboration-time interpreter does not model.
static std::optional<ConstVal> ConstEvalUserCall(const Expr* expr,
                                                 const ScopeMap& scope) {
  if (!g_const_func_registry || expr->callee.empty()) return std::nullopt;
  auto it = g_const_func_registry->find(expr->callee);
  if (it == g_const_func_registry->end() || it->second == nullptr)
    return std::nullopt;
  const ModuleItem* func = it->second;
  if (func->kind != ModuleItemKind::kFunctionDecl) return std::nullopt;
  if (g_const_func_depth >= kMaxConstFuncDepth) return std::nullopt;
  ++g_const_func_depth;
  struct DepthGuard {
    ~DepthGuard() { --g_const_func_depth; }
  } depth_guard;

  // The body sees the caller's parameter scope (a constant function may
  // reference module/package/$unit parameters, §13.4.3), overlaid with the
  // argument bindings and the implicit result variable.
  ScopeMap locals = scope;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const FunctionArg& fa = func->func_args[i];
    const Expr* arg_expr =
        i < expr->args.size() ? expr->args[i] : fa.default_value;
    if (!arg_expr) return std::nullopt;
    auto v = ConstEvalFull(arg_expr, scope);
    if (!v) return std::nullopt;
    if (!fa.name.empty()) locals[fa.name] = v->value;
  }
  if (!func->name.empty()) locals[func->name] = 0;

  int64_t iter_budget = kMaxConstFuncIterations;
  for (auto* s : func->func_body_stmts) {
    ConstFuncFlow flow = ExecConstFuncStmt(s, locals, func->name, iter_budget);
    if (flow == ConstFuncFlow::kAbort) return std::nullopt;
    if (flow == ConstFuncFlow::kReturn) break;
  }
  auto rit = locals.find(func->name);
  if (rit == locals.end()) return std::nullopt;
  return ConstVal{rit->second, 32, true};
}

std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return ConstEvalLiteral(expr);
    case ExprKind::kStringLiteral:
      return ConstEvalStringLiteral(expr);
    case ExprKind::kIdentifier: {
      // §3.12.1: a $unit:: prefix forces resolution to the compilation-unit
      // scope, bypassing any same-named local that would otherwise shadow it.
      // Those values are aliased under a "$unit::"-qualified key by
      // BuildParamScope, so a match there is the outermost declaration and a
      // miss must not silently fall back to the shadowing local.
      if (expr->scope_prefix == "$unit") {
        std::string key = "$unit::";
        key += expr->text;
        auto uit = scope.find(key);
        if (uit != scope.end()) return ConstVal{uit->second, 32, true};
        return std::nullopt;
      }
      auto it = scope.find(expr->text);
      if (it != scope.end()) return ConstVal{it->second, 32, true};
      return std::nullopt;
    }
    case ExprKind::kUnary:
      return ConstEvalUnaryFull(expr, scope);
    case ExprKind::kBinary:
      return ConstEvalBinaryFull(expr, scope);
    case ExprKind::kTernary: {
      auto cond = ConstEvalFull(expr->condition, scope);
      if (!cond) return std::nullopt;
      return ConstEvalFull(cond->value ? expr->true_expr : expr->false_expr,
                           scope);
    }
    case ExprKind::kConcatenation: {
      auto val = EvalConcat(expr, scope);
      if (!val) return std::nullopt;
      return ConstVal{*val, 32, false};
    }
    case ExprKind::kReplicate: {
      auto val = EvalReplicate(expr, scope);
      if (!val) return std::nullopt;
      return ConstVal{*val, 32, false};
    }
    case ExprKind::kSelect:
      return ConstEvalSelectFull(expr, scope);
    case ExprKind::kSystemCall:
      return ConstEvalSysCallFull(expr, scope);
    case ExprKind::kMemberAccess:
      return ConstEvalMemberAccessFull(expr, scope);
    case ExprKind::kCall:
      // §13.4.3: a call to a user-defined constant function folds at
      // elaboration time.
      return ConstEvalUserCall(expr, scope);
    default:
      return std::nullopt;
  }
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

static std::optional<double> EvalRealBinary(TokenKind op, double lhs,
                                            double rhs) {
  switch (op) {
    case TokenKind::kPlus:
      return lhs + rhs;
    case TokenKind::kMinus:
      return lhs - rhs;
    case TokenKind::kStar:
      return lhs * rhs;
    case TokenKind::kSlash:
      if (rhs == 0.0) return std::nullopt;
      return lhs / rhs;
    case TokenKind::kPower:
      return std::pow(lhs, rhs);
    default:
      return std::nullopt;
  }
}

static std::optional<double> EvalRealUnary(TokenKind op, double operand) {
  switch (op) {
    case TokenKind::kMinus:
      return -operand;
    case TokenKind::kPlus:
      return operand;
    default:
      return std::nullopt;
  }
}

std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kRealLiteral:
    // §5.8: a time literal is interpreted as a realtime (real) value already
    // scaled to the current time unit; the parser folds that scaling into
    // real_val, so in a constant real context it evaluates exactly like any
    // other real literal.
    case ExprKind::kTimeLiteral:
      return expr->real_val;
    case ExprKind::kIntegerLiteral:
      return static_cast<double>(expr->int_val);
    case ExprKind::kIdentifier: {
      auto it = scope.find(expr->text);
      if (it != scope.end()) return static_cast<double>(it->second);
      return std::nullopt;
    }
    case ExprKind::kUnary: {
      auto operand = ConstEvalReal(expr->lhs, scope);
      if (!operand) return std::nullopt;
      return EvalRealUnary(expr->op, *operand);
    }
    case ExprKind::kBinary: {
      auto lhs = ConstEvalReal(expr->lhs, scope);
      auto rhs = ConstEvalReal(expr->rhs, scope);
      if (!lhs || !rhs) return std::nullopt;
      return EvalRealBinary(expr->op, *lhs, *rhs);
    }
    case ExprKind::kTernary: {
      auto cond = ConstEvalInt(expr->condition, scope);
      if (!cond) return std::nullopt;
      return ConstEvalReal(*cond ? expr->true_expr : expr->false_expr, scope);
    }
    case ExprKind::kSystemCall:
    case ExprKind::kCall: {
      // §20.5: the real-returning conversion functions may appear in a constant
      // real context. Each folds from the constant integral value of its arg.
      if (expr->callee == "$itor") {
        if (expr->args.empty()) return std::nullopt;
        auto iv = ConstEvalInt(expr->args[0], scope);
        if (!iv) return std::nullopt;
        return static_cast<double>(*iv);
      }
      if (expr->callee == "$bitstoreal") {
        if (expr->args.empty()) return std::nullopt;
        auto iv = ConstEvalInt(expr->args[0], scope);
        if (!iv) return std::nullopt;
        uint64_t bits = static_cast<uint64_t>(*iv);
        double d = 0.0;
        std::memcpy(&d, &bits, sizeof(d));
        return d;
      }
      if (expr->callee == "$bitstoshortreal") {
        if (expr->args.empty()) return std::nullopt;
        auto iv = ConstEvalInt(expr->args[0], scope);
        if (!iv) return std::nullopt;
        uint32_t bits = static_cast<uint32_t>(*iv);
        float fv = 0.0f;
        std::memcpy(&fv, &bits, sizeof(fv));
        return static_cast<double>(fv);
      }
      return std::nullopt;
    }
    default:
      return std::nullopt;
  }
}

std::optional<double> ConstEvalReal(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalReal(expr, kEmptyScope);
}

bool IsConstantSysFunc(std::string_view name) {
  static const std::unordered_set<std::string_view> kConstSysFuncs = {
      "$clog2",
      "$bits",
      "$countones",
      "$onehot",
      "$onehot0",
      "$isunknown",
      "$isunbounded",

      "$timescale",
      "$timeprecision",

      "$itor",
      "$rtoi",
      "$bitstoreal",
      "$realtobits",
      "$bitstoshortreal",
      "$shortrealtobits",
      "$signed",
      "$unsigned",

      "$ln",
      "$log10",
      "$exp",
      "$sqrt",
      "$pow",
      "$floor",
      "$ceil",
      "$sin",
      "$cos",
      "$tan",
      "$asin",
      "$acos",
      "$atan",
      "$atan2",
      "$hypot",
      "$sinh",
      "$cosh",
      "$tanh",
      "$asinh",
      "$acosh",
      "$atanh",

      "$dimensions",
      "$unpacked_dimensions",
      "$left",
      "$right",
      "$low",
      "$high",
      "$increment",
      "$size",

      "$countbits",

      "$sformatf",
  };
  return kConstSysFuncs.count(name) > 0;
}

static bool AllElementsConstant(const std::vector<Expr*>& elems,
                                const ScopeMap& scope) {
  for (auto* elem : elems) {
    if (!IsConstantExpr(elem, scope)) return false;
  }
  return true;
}

static bool IsConstEvenWithNonConstArgs(std::string_view name) {
  static const std::unordered_set<std::string_view> kFuncs = {
      "$bits", "$dimensions", "$unpacked_dimensions", "$left", "$right",
      "$low",  "$high",       "$increment",           "$size",
  };
  return kFuncs.count(name) > 0;
}

static bool IsConstantSysCallExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantSysFunc(expr->callee)) return false;
  if (IsConstEvenWithNonConstArgs(expr->callee)) return true;
  return AllElementsConstant(expr->args, scope);
}

static bool IsTypeOnlyBuiltinMethod(std::string_view method) {
  static const std::unordered_set<std::string_view> kMethods = {
      "size", "num",   "bits", "dimensions", "unpacked_dimensions",
      "left", "right", "low",  "high",       "increment",
  };
  return kMethods.count(method) > 0;
}

static bool IsValueDependentBuiltinMethod(std::string_view method) {
  static const std::unordered_set<std::string_view> kMethods = {
      "len",
  };
  return kMethods.count(method) > 0;
}

static bool IsConstantBuiltinMethodCall(const Expr* expr,
                                        const ScopeMap& scope) {
  if (!expr) return false;
  const Expr* member = nullptr;
  if (expr->kind == ExprKind::kCall && expr->lhs &&
      expr->lhs->kind == ExprKind::kMemberAccess) {
    if (!AllElementsConstant(expr->args, scope)) return false;
    member = expr->lhs;
  } else if (expr->kind == ExprKind::kMemberAccess) {
    member = expr;
  } else {
    return false;
  }
  if (!member->rhs || member->rhs->kind != ExprKind::kIdentifier) return false;
  std::string_view method = member->rhs->text;
  if (IsTypeOnlyBuiltinMethod(method)) return true;
  if (IsValueDependentBuiltinMethod(method)) {
    return IsConstantExpr(member->lhs, scope);
  }
  return false;
}

static bool IsConstantSelectExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantExpr(expr->base, scope)) return false;
  if (!IsConstantExpr(expr->index, scope)) return false;
  if (expr->index_end && !IsConstantExpr(expr->index_end, scope)) return false;
  return true;
}

static bool IsConstantMemberAccessExpr(const Expr* expr,
                                       const ScopeMap& scope) {
  if (IsConstantBuiltinMethodCall(expr, scope)) return true;
  if (expr->lhs && expr->rhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->rhs->kind == ExprKind::kIdentifier) {
    std::string compound =
        std::string(expr->lhs->text) + "." + std::string(expr->rhs->text);
    return scope.count(compound) > 0;
  }
  return false;
}

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return false;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    case ExprKind::kIdentifier:
      return scope.count(expr->text) > 0;
    case ExprKind::kUnary:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kBinary:
      return IsConstantExpr(expr->lhs, scope) &&
             IsConstantExpr(expr->rhs, scope);
    case ExprKind::kTernary:
      return IsConstantExpr(expr->condition, scope) &&
             IsConstantExpr(expr->true_expr, scope) &&
             IsConstantExpr(expr->false_expr, scope);
    case ExprKind::kConcatenation:
      return AllElementsConstant(expr->elements, scope);
    case ExprKind::kReplicate:
      return IsConstantExpr(expr->repeat_count, scope) &&
             AllElementsConstant(expr->elements, scope);
    case ExprKind::kSelect:
      return IsConstantSelectExpr(expr, scope);
    case ExprKind::kSystemCall:
      return IsConstantSysCallExpr(expr, scope);
    case ExprKind::kCast:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kAssignmentPattern:
      return AllElementsConstant(expr->elements, scope);
    case ExprKind::kCall:
      if (IsConstantBuiltinMethodCall(expr, scope)) return true;
      return AllElementsConstant(expr->args, scope);
    case ExprKind::kMemberAccess:
      return IsConstantMemberAccessExpr(expr, scope);
    default:
      return false;
  }
}

struct StaticPrefixResult {
  std::string text;
  bool is_static;
};

static StaticPrefixResult BuildStaticPrefix(const Expr* expr,
                                            const ScopeMap& scope);

static StaticPrefixResult BuildIdentifierPrefix(const Expr* expr) {
  std::string result;
  if (!expr->scope_prefix.empty()) result += expr->scope_prefix;
  result += expr->text;
  return {result, true};
}

static StaticPrefixResult BuildMemberAccessPrefix(const Expr* expr,
                                                  const ScopeMap& scope) {
  if (!expr->lhs || !expr->rhs) return {"", false};
  auto base = BuildStaticPrefix(expr->lhs, scope);
  if (!base.is_static) return {base.text, false};
  return {base.text + "." + std::string(expr->rhs->text), true};
}

static StaticPrefixResult BuildSelectPrefix(const Expr* expr,
                                            const ScopeMap& scope) {
  auto base = BuildStaticPrefix(expr->base, scope);
  if (base.text.empty()) return {"", false};
  if (!base.is_static) return {base.text, false};
  auto idx = ConstEvalInt(expr->index, scope);
  if (!idx) return {base.text, false};
  return {base.text + "[" + std::to_string(*idx) + "]", true};
}

static StaticPrefixResult BuildStaticPrefix(const Expr* expr,
                                            const ScopeMap& scope) {
  if (!expr) return {"", false};

  if (expr->kind == ExprKind::kIdentifier) {
    return BuildIdentifierPrefix(expr);
  }

  if (expr->kind == ExprKind::kMemberAccess) {
    return BuildMemberAccessPrefix(expr, scope);
  }

  if (expr->kind == ExprKind::kSelect && expr->base) {
    return BuildSelectPrefix(expr, scope);
  }

  return {"", false};
}

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return "";
  return BuildStaticPrefix(expr, scope).text;
}

}  // namespace delta
