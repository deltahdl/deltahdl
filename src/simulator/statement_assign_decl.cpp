#include <algorithm>
#include <cmath>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

StmtResult ExecExprStmtImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto result = EvalExpr(stmt->expr, ctx, arena);

  if (stmt->expr && stmt->expr->kind == ExprKind::kSystemCall &&
      stmt->expr->callee == "$cast" && result.ToUint64() == 0) {
    ctx.GetDiag().Error({}, "runtime error: $cast failed — invalid assignment");
  }
  return StmtResult::kDone;
}

static void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                                     SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return;
  auto* dim = stmt->var_unpacked_dims[0];
  if (!dim || dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return;
  auto left = static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64());
  auto right = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  auto lo = static_cast<uint32_t>(std::min(left, right));
  auto size = static_cast<uint32_t>(std::abs(left - right) + 1);
  ArrayInfo info;
  info.lo = lo;
  info.size = size;
  info.elem_width = elem_width;
  info.is_descending = (left > right);
  ctx.RegisterArray(stmt->var_name, info);
  for (uint32_t i = 0; i < size; ++i) {
    uint32_t idx = lo + i;
    auto name = std::string(stmt->var_name) + "[" + std::to_string(idx) + "]";
    ctx.CreateVariable(*arena.Create<std::string>(std::move(name)), elem_width);
  }
}

static bool TryExecWeakRefVarDecl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->var_decl_type.type_name != "weak_reference") return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, "weak_reference");
  const auto& type_params = stmt->var_decl_type.type_params;
  if (!type_params.empty()) {
    std::vector<Expr*> exprs;
    for (const auto& tp : type_params) {
      exprs.push_back(tp.type_ref_expr);
    }
    ctx.SetVariableClassParamExprs(stmt->var_name, std::move(exprs));
  }
  if (!stmt->var_init || stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new")
    return true;
  uint64_t referent = kNullClassHandle;
  if (!stmt->var_init->args.empty()) {
    auto val = EvalExpr(stmt->var_init->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, wr_handle);
  return true;
}

// Records the class type-parameter override expressions (if any) for the
// just-created class variable `var_name`.
static void SetClassParamExprs(std::string_view var_name,
                               const std::vector<DataType>& type_params,
                               SimContext& ctx) {
  if (type_params.empty()) return;
  std::vector<Expr*> exprs;
  for (const auto& tp : type_params) {
    exprs.push_back(tp.type_ref_expr);
  }
  ctx.SetVariableClassParamExprs(var_name, std::move(exprs));
}

// Handles `T v = new src;` shallow-copy construction. Returns true if `init`
// names a copyable source object and the copy was installed into `var_name`.
static bool TryExecClassShallowCopy(std::string_view var_name, const Expr* init,
                                    SimContext& ctx, Arena& arena) {
  if (!init->lhs || init->lhs->kind != ExprKind::kIdentifier) return false;
  auto src_val = EvalExpr(init->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, copy_handle);
  return true;
}

static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  auto class_type = stmt->var_decl_type.type_name;
  if (class_type.empty() || !ctx.FindClassType(class_type)) return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, class_type);

  SetClassParamExprs(stmt->var_name, stmt->var_decl_type.type_params, ctx);

  if (!stmt->var_init) return true;
  if (stmt->var_init->kind != ExprKind::kCall) return true;
  if (stmt->var_init->text != "new") return true;

  if (TryExecClassShallowCopy(stmt->var_name, stmt->var_init, ctx, arena)) {
    return true;
  }

  auto handle = EvalClassNew(class_type, stmt->var_init, ctx, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = handle;
  ApplyClassParamOverrides(stmt->var_name, handle.ToUint64(), ctx, arena);
  return true;
}

static Variable* CreateVarInScope(std::string_view name, uint32_t width,
                                  SimContext& ctx) {
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

static void CreateDeclVariable(const Stmt* stmt, uint32_t width, bool is_real,
                               SimContext& ctx, Arena& arena) {
  if (width == 0 && stmt->var_decl_type.kind == DataTypeKind::kString) {
    CreateVarInScope(stmt->var_name, 0, ctx);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;
    if (is_real && width < 64) width = 64;
    CreateVarInScope(stmt->var_name, width, ctx);
    if (is_real) ctx.RegisterRealVariable(stmt->var_name);
    CreateBlockArrayElements(stmt, width, ctx, arena);
  }
}

// Returns true if the declaration resolves to an already-existing variable
// (a static-func var to alias, or a local already present) and so needs no
// fresh creation.
static bool TryReuseExistingDeclVar(const Stmt* stmt,
                                    std::string_view func_name,
                                    SimContext& ctx) {
  if (stmt->var_is_static && !func_name.empty()) {
    auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
    if (existing) {
      ctx.AliasLocalVariable(stmt->var_name, existing);
      return true;
    }
  } else if (!stmt->var_is_automatic) {
    if (ctx.HasLocalScope() && ctx.FindLocalVariable(stmt->var_name)) {
      return true;
    }
  }
  return false;
}

// Applies 4-state coercion and the optional initializer to a freshly created
// variable, then records it as a static-func var when applicable.
static void InitializeDeclVariable(const Stmt* stmt, Variable* var,
                                   std::string_view func_name, SimContext& ctx,
                                   Arena& arena) {
  var->is_4state = Is4stateType(stmt->var_decl_type.kind);
  if (!var->is_4state) CoerceTo2State(var->value);
  if (stmt->var_init) {
    var->value = EvalExpr(stmt->var_init, ctx, arena);
    if (!var->is_4state) CoerceTo2State(var->value);
  }

  if (stmt->var_is_static && !func_name.empty()) {
    ctx.SaveStaticFuncVar(func_name, stmt->var_name, var);
  }
}

StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (TryExecWeakRefVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;

  auto func_name = ctx.CurrentFuncName();
  if (TryReuseExistingDeclVar(stmt, func_name, ctx)) return StmtResult::kDone;

  uint32_t width = EvalTypeWidth(stmt->var_decl_type);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  CreateDeclVariable(stmt, width, is_real, ctx, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) {
    InitializeDeclVariable(stmt, var, func_name, ctx, arena);
  }
  return StmtResult::kDone;
}

static void CollectExprVars(const Expr* expr, SimContext& ctx,
                            std::vector<Variable*>& vars) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->text);
    if (var) vars.push_back(var);
    return;
  }
  CollectExprVars(expr->lhs, ctx, vars);
  CollectExprVars(expr->rhs, ctx, vars);
  CollectExprVars(expr->condition, ctx, vars);
  CollectExprVars(expr->true_expr, ctx, vars);
  CollectExprVars(expr->false_expr, ctx, vars);
  CollectExprVars(expr->base, ctx, vars);
  CollectExprVars(expr->index, ctx, vars);
  CollectExprVars(expr->index_end, ctx, vars);
  CollectExprVars(expr->with_expr, ctx, vars);
  CollectExprVars(expr->repeat_count, ctx, vars);
  for (auto* e : expr->elements) CollectExprVars(e, ctx, vars);
  for (auto* a : expr->args) CollectExprVars(a, ctx, vars);
}

// Applies a procedural continuous-assignment forced value to `var` from the
// expression `rhs`, then installs watchers on each variable appearing in `rhs`
// so the forced value is re-evaluated whenever those variables change.
static void InstallForcedValueWatcher(Variable* var, const Expr* rhs,
                                      SimContext& ctx, Arena& arena) {
  auto rhs_val = EvalExpr(rhs, ctx, arena);
  var->is_forced = true;
  var->forced_value = rhs_val;
  var->value = rhs_val;
  if (!var->is_4state) CoerceTo2State(var->value);
  var->proc_cont_rhs = rhs;
  var->NotifyWatchers();

  std::vector<Variable*> rhs_vars;
  CollectExprVars(rhs, ctx, rhs_vars);

  std::sort(rhs_vars.begin(), rhs_vars.end());
  rhs_vars.erase(std::unique(rhs_vars.begin(), rhs_vars.end()), rhs_vars.end());
  rhs_vars.erase(std::remove(rhs_vars.begin(), rhs_vars.end(), var),
                 rhs_vars.end());

  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : rhs_vars) {
    rhs_var->AddWatcher([var, rhs, ctx_ptr, arena_ptr]() {
      if (!var->is_forced || var->proc_cont_rhs != rhs) return true;
      auto new_val = EvalExpr(rhs, *ctx_ptr, *arena_ptr);
      var->forced_value = new_val;
      var->value = new_val;
      if (!var->is_4state) CoerceTo2State(var->value);
      var->NotifyWatchers();
      return false;
    });
  }
}

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  if (stmt->kind == StmtKind::kAssign) var->assign_cont_rhs = stmt->rhs;
  InstallForcedValueWatcher(var, stmt->rhs, ctx, arena);

  return StmtResult::kDone;
}

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  var->is_forced = false;
  var->proc_cont_rhs = nullptr;

  if (stmt->kind == StmtKind::kDeassign) {
    var->assign_cont_rhs = nullptr;
  } else if (stmt->lhs->kind == ExprKind::kIdentifier) {
    if (auto* net = ctx.FindNet(stmt->lhs->text)) {
      net->Resolve(arena);
    }
  }

  if (var->assign_cont_rhs && stmt->kind != StmtKind::kDeassign) {
    InstallForcedValueWatcher(var, var->assign_cont_rhs, ctx, arena);
  }

  return StmtResult::kDone;
}

}  // namespace delta
