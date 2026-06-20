#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

static int ResolveArgIndex(const ModuleItem* func, const Expr* expr,
                           size_t param_idx) {
  if (expr->arg_names.empty()) {
    return (param_idx < expr->args.size()) ? static_cast<int>(param_idx) : -1;
  }

  size_t positional_count = expr->args.size() - expr->arg_names.size();
  if (param_idx < positional_count) {
    return static_cast<int>(param_idx);
  }
  auto param_name = func->func_args[param_idx].name;
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == param_name)
      return static_cast<int>(positional_count + j);
  }
  return -1;
}

static bool TryBindRefArg(const Expr* expr, int arg_index,
                          std::string_view param_name, SimContext& ctx) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  auto* target = ctx.FindVariable(call_arg->text);
  if (!target) return false;
  ctx.AliasLocalVariable(param_name, target);
  return true;
}

static bool TryBindQueueElementRef(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kSelect) return false;
  if (!call_arg->base || call_arg->base->kind != ExprKind::kIdentifier)
    return false;
  auto* q = ctx.FindQueue(call_arg->base->text);
  if (!q || !call_arg->index) return false;
  auto idx = EvalExpr(call_arg->index, ctx, arena).ToUint64();
  if (idx >= q->elements.size()) return false;

  if (param.data_type.kind != DataTypeKind::kImplicit) {
    uint32_t param_width = EvalTypeWidth(param.data_type);
    if (param_width != q->elem_width) return false;
  }

  auto* var = ctx.CreateLocalVariable(param.name, q->elem_width);
  var->value = q->elements[idx];

  if (idx < q->element_ids.size()) {
    ctx.RecordQueueRef({q, q->element_ids[idx], var});
  }
  return true;
}

void WritebackQueueRefs(SimContext& ctx) {
  auto bindings = ctx.PopQueueRefFrame();
  for (const auto& b : bindings) {
    auto& ids = b.queue->element_ids;
    auto it = std::find(ids.begin(), ids.end(), b.element_id);
    if (it == ids.end()) continue;
    auto pos = static_cast<size_t>(it - ids.begin());
    if (pos < b.queue->elements.size()) {
      b.queue->elements[pos] = b.local_var->value;
    }
  }
}

static bool TryBindAssocElementRef(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kSelect) return false;
  if (!call_arg->base || call_arg->base->kind != ExprKind::kIdentifier)
    return false;
  auto* aa = ctx.FindAssocArray(call_arg->base->text);
  if (!aa || !call_arg->index) return false;

  auto* var = ctx.CreateLocalVariable(param.name, aa->elem_width);

  AssocRefBinding binding;
  binding.assoc = aa;
  binding.is_string_key = aa->is_string_key;
  binding.local_var = var;
  if (aa->is_string_key) {
    binding.str_key =
        FormatValueAsString(EvalExpr(call_arg->index, ctx, arena));
    auto it = aa->str_data.find(binding.str_key);
    if (it == aa->str_data.end()) {
      aa->str_data[binding.str_key] = MakeLogic4Vec(arena, aa->elem_width);
      it = aa->str_data.find(binding.str_key);
    }
    var->value = it->second;
  } else {
    binding.int_key =
        static_cast<int64_t>(EvalExpr(call_arg->index, ctx, arena).ToUint64());
    auto it = aa->int_data.find(binding.int_key);
    if (it == aa->int_data.end()) {
      aa->int_data[binding.int_key] = MakeLogic4Vec(arena, aa->elem_width);
      it = aa->int_data.find(binding.int_key);
    }
    var->value = it->second;
  }
  ctx.RecordAssocRef(binding);
  return true;
}

void WritebackAssocRefs(SimContext& ctx) {
  auto bindings = ctx.PopAssocRefFrame();
  for (const auto& b : bindings) {
    if (b.is_string_key) {
      b.assoc->str_data[b.str_key] = b.local_var->value;
    } else {
      b.assoc->int_data[b.int_key] = b.local_var->value;
    }
  }
}

static Logic4Vec ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                 int arg_index, SimContext& ctx, Arena& arena) {
  if (arg_index >= 0 && expr->args[static_cast<size_t>(arg_index)] != nullptr) {
    return EvalExpr(expr->args[static_cast<size_t>(arg_index)], ctx, arena);
  }
  if (param.default_value) return EvalExpr(param.default_value, ctx, arena);
  return MakeLogic4Vec(arena, 32);
}

static bool TryBindAssocArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  auto* src = ctx.FindAssocArray(call_arg->text);
  if (!src) return false;
  auto* dst =
      ctx.CreateAssocArray(param_name, src->elem_width, src->is_string_key);
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  return true;
}

static bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, formal.name, ctx)) return true;

  // Dynamic arrays and queues hold their elements in a QueueObject rather than
  // as per-element variables, so a by-value bind copies through that object;
  // the formal becomes a fresh, independent copy of the actual.
  if (auto* src_q = ctx.FindQueue(call_arg->text)) {
    if (formal.unpacked_dims.empty()) return false;
    if (formal.unpacked_dims[0] != nullptr) {
      // A fixed-size formal accepts a dynamic array or queue only when the
      // sizes are equal; this can only be verified at the time of the call.
      auto formal_size =
          EvalExpr(formal.unpacked_dims[0], ctx, arena).ToUint64();
      if (src_q->elements.size() != formal_size) {
        ctx.GetDiag().Error({}, "array size mismatch: formal expects " +
                                    std::to_string(formal_size) +
                                    " elements, actual has " +
                                    std::to_string(src_q->elements.size()));
        return true;
      }
      ArrayInfo finfo;
      finfo.size = static_cast<uint32_t>(formal_size);
      finfo.elem_width = src_q->elem_width;
      finfo.is_4state = src_q->is_4state;
      ctx.RegisterArray(formal.name, finfo);
      for (uint32_t j = 0; j < finfo.size; ++j) {
        auto dst = std::string(formal.name) + "[" + std::to_string(j) + "]";
        auto* dst_var =
            ctx.CreateLocalVariable(*arena.Create<std::string>(std::move(dst)),
                                    src_q->elements[j].width);
        dst_var->value = src_q->elements[j];
      }
      return true;
    }
    // An unsized formal keeps the dynamic-array/queue representation, so the
    // callee reads the copy through the same queue-backed select path.
    auto* dst_q = ctx.CreateQueue(formal.name, src_q->elem_width,
                                  src_q->max_size, src_q->is_4state);
    dst_q->elements = src_q->elements;
    dst_q->AssignFreshIds();
    return true;
  }

  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;

  ctx.RegisterArray(formal.name, *info);
  for (uint32_t j = 0; j < info->size; ++j) {
    uint32_t idx = info->lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(formal.name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info->elem_width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    dst_var->value = val;
  }
  return true;
}

void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    int ai = ResolveArgIndex(func, expr, i);
    auto dir = func->func_args[i].direction;
    if (dir == Direction::kRef) {
      if (TryBindRefArg(expr, ai, func->func_args[i].name, ctx)) continue;
      if (TryBindQueueElementRef(expr, ai, func->func_args[i], ctx, arena))
        continue;
      if (TryBindAssocElementRef(expr, ai, func->func_args[i], ctx, arena))
        continue;
    }
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)],
                                   func->func_args[i], ctx, arena)) {
      continue;
    }
    auto val = ResolveArgValue(func->func_args[i], expr, ai, ctx, arena);
    const auto& dt = func->func_args[i].data_type;
    if (dt.kind != DataTypeKind::kImplicit) {
      uint32_t formal_width = EvalTypeWidth(dt);
      if (formal_width > 0 && formal_width != val.width)
        val = ResizeToWidth(val, formal_width, arena);
    }
    auto* var = ctx.CreateLocalVariable(func->func_args[i].name, val.width);
    var->value = val;
  }
}

void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    auto* local = ctx.FindLocalVariable(func->func_args[i].name);
    if (!local) continue;
    int ai = ResolveArgIndex(func, expr, i);
    const Expr* wb_target = nullptr;
    if (ai >= 0) wb_target = expr->args[static_cast<size_t>(ai)];
    if (!wb_target) wb_target = func->func_args[i].default_value;
    if (!wb_target) continue;
    PerformBlockingAssign(wb_target, local->value, ctx, arena);
  }
}

static void ExecFuncSelectAssign(const Expr* lhs, const Logic4Vec& val,
                                 SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (aa && lhs->index) {
    if (aa->is_string_key) {
      aa->str_data[FormatValueAsString(EvalExpr(lhs->index, ctx, arena))] = val;
    } else {
      auto key =
          static_cast<int64_t>(EvalExpr(lhs->index, ctx, arena).ToUint64());
      aa->int_data[key] = val;
    }
    return;
  }
  auto idx = EvalExpr(lhs->index, ctx, arena).ToUint64();
  auto name = std::string(lhs->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(name);
  if (elem) elem->value = val;
}

static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) {
      var->value = val;
      return;
    }
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->text), val);
    return;
  }
  if (stmt->lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(stmt->lhs, val, ctx, arena);
    return;
  }

  if (stmt->lhs->kind == ExprKind::kMemberAccess && stmt->lhs->lhs &&
      stmt->lhs->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->lhs->text == "this" && stmt->lhs->rhs &&
      stmt->lhs->rhs->kind == ExprKind::kIdentifier) {
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->rhs->text), val);
    return;
  }

  if (stmt->lhs->kind == ExprKind::kMemberAccess && stmt->lhs->lhs &&
      stmt->lhs->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->lhs->text == "super" && stmt->lhs->rhs &&
      stmt->lhs->rhs->kind == ExprKind::kIdentifier) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(std::string(stmt->lhs->rhs->text),
                               self->type->parent, val);
    }
  }
}

static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var,
                         std::string_view func_name, SimContext& ctx,
                         Arena& arena);
static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena);

// Returns the trailing unconditional else of an if/else-if chain, or null when
// the chain has no final else.
static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

// A unique/unique0/priority if encountered while running a function or task
// body performs the same violation checks as one in a process body (§12.4.2).
// Because the report queue is keyed on the calling process (§12.4.2.2), routing
// the report through AddPendingViolation attributes it to whichever process
// invoked the subroutine; separate callers therefore accumulate and flush
// independently.
static bool ExecFuncUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             Variable* ret_var, std::string_view func_name,
                             SimContext& ctx, Arena& arena) {
  int match_count = 0;
  const Stmt* first_match = nullptr;
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      match_count++;
      if (!first_match) first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (match_count > 1) {
    ctx.AddPendingViolation("unique if: multiple conditions matched");
  }
  if (first_match) {
    return ExecFuncStmt(first_match->then_branch, ret_var, func_name, ctx,
                        arena);
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else)
      return ExecFuncStmt(final_else, ret_var, func_name, ctx, arena);
  } else if (qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation("unique if: no condition matched");
  }
  return false;
}

static bool ExecFuncPriorityIf(const Stmt* stmt, Variable* ret_var,
                               std::string_view func_name, SimContext& ctx,
                               Arena& arena) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      return ExecFuncStmt(cur->then_branch, ret_var, func_name, ctx, arena);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else)
      return ExecFuncStmt(final_else, ret_var, func_name, ctx, arena);
  } else {
    ctx.AddPendingViolation("priority if: no condition matched");
  }
  return false;
}

static bool ExecFuncIf(const Stmt* stmt, Variable* ret_var,
                       std::string_view func_name, SimContext& ctx,
                       Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);

  auto qual = stmt->qualifier;
  bool r = false;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = ExecFuncUniqueIf(stmt, qual, ret_var, func_name, ctx, arena);
  } else if (qual == CaseQualifier::kPriority) {
    r = ExecFuncPriorityIf(stmt, ret_var, func_name, ctx, arena);
  } else {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() != 0) {
      r = ExecFuncStmt(stmt->then_branch, ret_var, func_name, ctx, arena);
    } else if (stmt->else_branch) {
      r = ExecFuncStmt(stmt->else_branch, ret_var, func_name, ctx, arena);
    } else {
      r = false;
    }
  }

  if (labeled) ctx.PopStaticScope(stmt->label);
  return r;
}

static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena) {
  bool named = !stmt->label.empty();
  if (named) ctx.PushStaticScope(stmt->label);
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, ret_var, func_name, ctx, arena)) {
      if (named) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (named) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncFor(const Stmt* stmt, Variable* ret_var,
                        std::string_view func_name, SimContext& ctx,
                        Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  bool scoped = false;
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) {
      scoped = true;
      break;
    }
  }
  if (scoped) ctx.PushScope();
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    auto* init = stmt->for_inits[i];
    if (i < stmt->for_init_types.size() &&
        stmt->for_init_types[i].kind != DataTypeKind::kImplicit && init &&
        init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
      if (w == 0) w = 32;
      auto* v = ctx.CreateLocalVariable(init->lhs->text, w);
      if (init->rhs) v->value = EvalExpr(init->rhs, ctx, arena);
    } else if (init) {
      ExecFuncStmt(init, ret_var, func_name, ctx, arena);
    }
  }
  while (stmt->for_cond && EvalExpr(stmt->for_cond, ctx, arena).IsTruthy()) {
    if (stmt->for_body &&
        ExecFuncStmt(stmt->for_body, ret_var, func_name, ctx, arena)) {
      if (scoped) ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
    for (auto* step : stmt->for_steps)
      ExecFuncStmt(step, ret_var, func_name, ctx, arena);
  }
  if (scoped) ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  uint32_t w = EvalTypeWidth(type);
  if (w == 0) w = 32;
  auto* v = ctx.CreateLocalVariable(name, w);
  if (init) v->value = EvalExpr(init, ctx, arena);
  return v;
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init, ctx,
                     arena);
}

static void ExecFuncVarDeclStatic(const Stmt* stmt, std::string_view func_name,
                                  SimContext& ctx, Arena& arena) {
  auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
  if (existing) {
    ctx.AliasLocalVariable(stmt->var_name, existing);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, ctx, arena);
  ctx.SaveStaticFuncVar(func_name, stmt->var_name, v);
}

static void ExecFuncVarDecl(const Stmt* stmt, std::string_view func_name,
                            SimContext& ctx, Arena& arena) {
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, ctx, arena);
    return;
  }
  if (stmt->var_is_static) {
    ExecFuncVarDeclStatic(stmt, func_name, ctx, arena);
    return;
  }
  if (ctx.FindLocalVariable(stmt->var_name)) return;
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init, ctx,
                     arena);
}

static std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

static bool ExecFuncWhile(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (stmt->condition && EvalExpr(stmt->condition, ctx, arena).IsTruthy()) {
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncDoWhile(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  do {
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  } while (stmt->condition && EvalExpr(stmt->condition, ctx, arena).IsTruthy());
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncForever(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  for (;;) {
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncForeach(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::string name = GetForeachArrayName(stmt->expr);
  if (name.empty()) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    return false;
  }
  uint32_t size = 0;
  auto* info = ctx.FindArrayInfo(name);
  if (info) {
    size = info->size;
  } else {
    auto* var = ctx.FindVariable(name);
    if (var) size = var->value.width;
  }
  if (size == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    return false;
  }

  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size; ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(arena, 32, i);
    }
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }

  ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var,
                         std::string_view func_name, SimContext& ctx,
                         Arena& arena) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr)
        ret_var->value = EvalExpr(stmt->expr, ctx, arena, ret_var->value.width);
      return true;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, ctx, arena);
      return false;
    case StmtKind::kExprStmt:
      EvalExpr(stmt->expr, ctx, arena);
      return false;
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, func_name, ctx, arena);
      return false;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kWhile:
      return ExecFuncWhile(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecFuncDoWhile(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kForever:
      return ExecFuncForever(stmt, ret_var, func_name, ctx, arena);
    default:
      return false;
  }
}

void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena) {
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, ret_var, func->name, ctx, arena)) return;
  }
}

}  // namespace delta
