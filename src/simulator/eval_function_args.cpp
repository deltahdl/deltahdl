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

// Binds a dynamic-array/queue actual to a fixed-size formal: the sizes must
// match, after which the formal is materialized as per-element variables.
static bool BindQueueToFixedFormal(QueueObject* src_q,
                                   const FunctionArg& formal, SimContext& ctx,
                                   Arena& arena) {
  // A fixed-size formal accepts a dynamic array or queue only when the
  // sizes are equal; this can only be verified at the time of the call.
  auto formal_size = EvalExpr(formal.unpacked_dims[0], ctx, arena).ToUint64();
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
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), src_q->elements[j].width);
    dst_var->value = src_q->elements[j];
  }
  return true;
}

// Dynamic arrays and queues hold their elements in a QueueObject rather than
// as per-element variables, so a by-value bind copies through that object;
// the formal becomes a fresh, independent copy of the actual.
static bool TryBindQueueArg(QueueObject* src_q, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (formal.unpacked_dims.empty()) return false;
  if (formal.unpacked_dims[0] != nullptr) {
    return BindQueueToFixedFormal(src_q, formal, ctx, arena);
  }
  // An unsized formal keeps the dynamic-array/queue representation, so the
  // callee reads the copy through the same queue-backed select path.
  auto* dst_q = ctx.CreateQueue(formal.name, src_q->elem_width, src_q->max_size,
                                src_q->is_4state);
  dst_q->elements = src_q->elements;
  dst_q->AssignFreshIds();
  return true;
}

// Binds a fixed-size unpacked-array actual by copying each element variable
// into a fresh per-element formal variable.
static void BindFixedArrayArg(const Expr* call_arg, const FunctionArg& formal,
                              const ArrayInfo& info, SimContext& ctx,
                              Arena& arena) {
  ctx.RegisterArray(formal.name, info);
  for (uint32_t j = 0; j < info.size; ++j) {
    uint32_t idx = info.lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(formal.name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info.elem_width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    dst_var->value = val;
  }
}

static bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, formal.name, ctx)) return true;

  if (auto* src_q = ctx.FindQueue(call_arg->text)) {
    return TryBindQueueArg(src_q, formal, ctx, arena);
  }

  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;

  BindFixedArrayArg(call_arg, formal, *info, ctx, arena);
  return true;
}

// Attempts the ref-binding strategies (plain ref, queue element, assoc element)
// for a ref-direction formal. Returns true when one of them bound the argument.
static bool TryBindRefDirectionArg(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (TryBindRefArg(expr, arg_index, param.name, ctx)) return true;
  if (TryBindQueueElementRef(expr, arg_index, param, ctx, arena)) return true;
  if (TryBindAssocElementRef(expr, arg_index, param, ctx, arena)) return true;
  return false;
}

// Performs the default by-value bind: resolves the argument value, widens it to
// the formal's declared width when applicable, and creates the local variable.
// Computes a value parameter's declared width using the live simulation scope,
// so a width that references in-scope (class/specialization) parameters -- e.g.
// `logic [W-1:0]` -- resolves to the bound parameter value instead of
// collapsing to 1 bit. Types without packed dimensions use the static
// evaluator.
static uint32_t EvalFormalArgWidth(const DataType& dt, SimContext& ctx,
                                   Arena& arena) {
  if (!dt.packed_dim_left || !dt.packed_dim_right) return EvalTypeWidth(dt);
  auto span = [&](const Expr* l, const Expr* r) -> uint32_t {
    int64_t lv = static_cast<int64_t>(EvalExpr(l, ctx, arena).ToUint64());
    int64_t rv = static_cast<int64_t>(EvalExpr(r, ctx, arena).ToUint64());
    return static_cast<uint32_t>((lv >= rv ? lv - rv : rv - lv) + 1);
  };
  uint32_t width = span(dt.packed_dim_left, dt.packed_dim_right);
  for (const auto& [l, r] : dt.extra_packed_dims) width *= span(l, r);
  return width;
}

// §7.2.2/§13.5.1: make member access (arg.field) work on a by-value struct
// copy. struct_types_ is keyed by variable name, so a named-type formal -- e.g.
// `input s_t arg` -- cannot find its layout by the type name `s_t` (a type name
// is never a registered struct key). Resolve the layout from the actual
// argument's registered struct type and re-register it under the parameter
// name. No-op when the actual argument is not a resolvable struct identifier.
static void RegisterValueArgStructType(const FunctionArg& param,
                                       const Expr* expr, int arg_index,
                                       SimContext& ctx) {
  const Expr* actual =
      (arg_index >= 0) ? expr->args[static_cast<size_t>(arg_index)] : nullptr;
  if (actual && actual->kind == ExprKind::kIdentifier) {
    if (const auto* sinfo = ctx.GetVariableStructType(actual->text)) {
      // Copy before re-inserting: registering into struct_types_ may rehash and
      // invalidate the reference returned for the source variable.
      StructTypeInfo copy = *sinfo;
      ctx.RegisterStructType(param.name, copy);
      ctx.SetVariableStructType(param.name, param.name);
      return;
    }
  }
  // Legacy fallback for an inline struct-typed formal whose actual is not a
  // resolvable struct identifier.
  if (param.data_type.kind == DataTypeKind::kStruct &&
      !param.data_type.type_name.empty())
    ctx.SetVariableStructType(param.name, param.data_type.type_name);
}

static void BindValueArg(const FunctionArg& param, const Expr* expr,
                         int arg_index, SimContext& ctx, Arena& arena) {
  auto val = ResolveArgValue(param, expr, arg_index, ctx, arena);
  const auto& dt = param.data_type;
  if (dt.kind != DataTypeKind::kImplicit) {
    uint32_t formal_width = EvalFormalArgWidth(dt, ctx, arena);
    if (formal_width > 0 && formal_width != val.width)
      val = ResizeToWidth(val, formal_width, arena);
  }
  auto* var = ctx.CreateLocalVariable(param.name, val.width);
  var->value = val;
  // A named-type struct formal (input s_t arg) has kind kNamed, not kStruct, so
  // resolve from the actual argument unconditionally; the resolver is a no-op
  // for non-struct actuals.
  RegisterValueArgStructType(param, expr, arg_index, ctx);
}

void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    int ai = ResolveArgIndex(func, expr, i);
    const auto& param = func->func_args[i];
    if (param.direction == Direction::kRef &&
        TryBindRefDirectionArg(expr, ai, param, ctx, arena)) {
      continue;
    }
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)], param,
                                   ctx, arena)) {
      continue;
    }
    BindValueArg(param, expr, ai, ctx, arena);
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

// True when lhs is a `<base>.<member>` member access whose base identifier name
// matches base_name and whose member is a plain identifier.
static bool IsMemberAccessOn(const Expr* lhs, std::string_view base_name) {
  return lhs->kind == ExprKind::kMemberAccess && lhs->lhs &&
         lhs->lhs->kind == ExprKind::kIdentifier &&
         lhs->lhs->text == base_name && lhs->rhs &&
         lhs->rhs->kind == ExprKind::kIdentifier;
}

// §8.15/§8.18: an unqualified (or `this`-qualified) member write inside a
// method resolves the member in the lexically enclosing class's scope. Routing
// through SetPropertyForType keyed by the current method's class updates the
// scoped storage slot that a later qualified read (`obj.name`, `super.name`, or
// access through a base-typed handle) consults -- so a base constructor that
// runs as part of a chain populates the inherited slot, not just the unscoped
// alias. With no enclosing-class context active, the plain unscoped write is
// preserved, leaving non-method writes unchanged.
static void WriteSelfProperty(ClassObject* self, std::string_view name,
                              const Logic4Vec& val, SimContext& ctx) {
  // §8.11: a `this.x` write updates the invoking instance. Properties are kept
  // under both an unscoped key and a `Type::name` scoped key, and reads consult
  // the scoped key first. In a plain instance method (no enclosing-class
  // context, unlike a constructor) fall back to the object's own type so both
  // copies stay in sync; otherwise the write lands only on the unscoped key and
  // the next read returns the stale scoped value.
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!enclosing) enclosing = self->type;
  if (enclosing) {
    self->SetPropertyForType(name, enclosing, val);
  } else {
    self->SetProperty(std::string(name), val);
  }
}

// Assigns to a plain identifier lhs: writes the local variable when present,
// otherwise falls back to a property on the current `this` object.
static void ExecFuncIdentifierAssign(const Expr* lhs, const Logic4Vec& val,
                                     SimContext& ctx) {
  auto* var = ctx.FindVariable(lhs->text);
  if (var) {
    var->value = val;
    return;
  }
  // §8.10: a static method writes a static property of the enclosing class by
  // unqualified reference (mirrors the read path in EvalIdentifier). Static
  // storage takes precedence over an instance property of the same name.
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls) {
    auto it = method_cls->static_properties.find(std::string(lhs->text));
    if (it != method_cls->static_properties.end()) {
      it->second = val;
      return;
    }
  }
  auto* self = ctx.CurrentThis();
  if (self) WriteSelfProperty(self, lhs->text, val, ctx);
}

static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  // §7.10/§13.4: an assignment to a queue from a function body uses the queue
  // assignment path -- it rebuilds the element list, allocates fresh element
  // ids, and bumps the generation so prior references are outdated -- rather
  // than a flat scalar write that ignores the queue object.
  // TryQueueBlockingAssign guards on an identifier queue target and declines
  // otherwise.
  if (TryQueueBlockingAssign(stmt, ctx, arena)) return;
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    ExecFuncIdentifierAssign(stmt->lhs, val, ctx);
    return;
  }
  if (stmt->lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(stmt->lhs, val, ctx, arena);
    return;
  }

  if (IsMemberAccessOn(stmt->lhs, "this")) {
    auto* self = ctx.CurrentThis();
    if (self) WriteSelfProperty(self, stmt->lhs->rhs->text, val, ctx);
    return;
  }

  if (IsMemberAccessOn(stmt->lhs, "super")) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(std::string(stmt->lhs->rhs->text),
                               self->type->parent, val);
    }
  }
}

// The environment in which a subroutine body executes (§13.4): the return
// variable that a `return` writes, the subroutine name used to key static
// function-local variables (§13.4.2), and the simulation/evaluation context.
// This quartet travels together through the entire recursive statement
// executor, so it is bundled into one entity rather than passed field by
// field.
struct FuncExecCtx {
  Variable* ret_var;
  std::string_view func_name;
  SimContext& ctx;
  Arena& arena;
};

static bool ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec);
static bool ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec);

// Returns the trailing unconditional else of an if/else-if chain, or null when
// the chain has no final else.
static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

// Aggregated result of evaluating the conditions of a unique-if chain.
struct UniqueIfScan {
  int match_count = 0;
  const Stmt* first_match = nullptr;
  bool has_final_else = false;
};

// Evaluates every condition in the if/else-if chain in source order, recording
// how many matched, the first match, and whether the chain ends in a final
// else.
static UniqueIfScan ScanUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  UniqueIfScan scan;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      scan.match_count++;
      if (!scan.first_match) scan.first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      scan.has_final_else = true;
    }
  }
  return scan;
}

// Runs the branch selected by a unique-if scan: the first matching arm, else
// the trailing unconditional else, reporting a no-match violation for a plain
// `unique` chain that has no final else.
static bool ExecFuncUniqueIfBranch(const Stmt* stmt, const UniqueIfScan& scan,
                                   CaseQualifier qual,
                                   const FuncExecCtx& exec) {
  if (scan.first_match) {
    return ExecFuncStmt(scan.first_match->then_branch, exec);
  }
  if (scan.has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else if (qual == CaseQualifier::kUnique) {
    exec.ctx.AddPendingViolation("unique if: no condition matched");
  }
  return false;
}

// A unique/unique0/priority if encountered while running a function or task
// body performs the same violation checks as one in a process body (§12.4.2).
// Because the report queue is keyed on the calling process (§12.4.2.2), routing
// the report through AddPendingViolation attributes it to whichever process
// invoked the subroutine; separate callers therefore accumulate and flush
// independently.
static bool ExecFuncUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             const FuncExecCtx& exec) {
  UniqueIfScan scan = ScanUniqueIfChain(stmt, exec.ctx, exec.arena);
  if (scan.match_count > 1) {
    exec.ctx.AddPendingViolation("unique if: multiple conditions matched");
  }
  return ExecFuncUniqueIfBranch(stmt, scan, qual, exec);
}

static bool ExecFuncPriorityIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, exec.ctx, exec.arena).IsTruthy()) {
      return ExecFuncStmt(cur->then_branch, exec);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else {
    exec.ctx.AddPendingViolation("priority if: no condition matched");
  }
  return false;
}

static bool ExecFuncIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);

  auto qual = stmt->qualifier;
  bool r = false;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = ExecFuncUniqueIf(stmt, qual, exec);
  } else if (qual == CaseQualifier::kPriority) {
    r = ExecFuncPriorityIf(stmt, exec);
  } else {
    auto cond = EvalExpr(stmt->condition, exec.ctx, exec.arena);
    if (cond.ToUint64() != 0) {
      r = ExecFuncStmt(stmt->then_branch, exec);
    } else if (stmt->else_branch) {
      r = ExecFuncStmt(stmt->else_branch, exec);
    } else {
      r = false;
    }
  }

  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return r;
}

static bool ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec) {
  bool named = !stmt->label.empty();
  if (named) exec.ctx.PushStaticScope(stmt->label);
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, exec)) {
      if (named) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (named) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

// True when any for-loop init declares a new variable (has an explicit type),
// which requires a fresh scope to hold the loop-local declarations.
static bool ForInitNeedsScope(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

// Runs the for-loop initializers: typed inits create loop-local variables,
// while untyped inits execute as ordinary statements.
static void ExecFuncForInits(const Stmt* stmt, const FuncExecCtx& exec) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    auto* init = stmt->for_inits[i];
    if (i < stmt->for_init_types.size() &&
        stmt->for_init_types[i].kind != DataTypeKind::kImplicit && init &&
        init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
      if (w == 0) w = 32;
      auto* v = exec.ctx.CreateLocalVariable(init->lhs->text, w);
      if (init->rhs) v->value = EvalExpr(init->rhs, exec.ctx, exec.arena);
    } else if (init) {
      ExecFuncStmt(init, exec);
    }
  }
}

// Runs the condition/body/step iterations of a for-loop. Returns true when the
// body executed a return (so the caller should propagate it).
static bool ExecFuncForLoop(const Stmt* stmt, const FuncExecCtx& exec) {
  while (stmt->for_cond &&
         EvalExpr(stmt->for_cond, exec.ctx, exec.arena).IsTruthy()) {
    if (stmt->for_body && ExecFuncStmt(stmt->for_body, exec)) {
      return true;
    }
    for (auto* step : stmt->for_steps) ExecFuncStmt(step, exec);
  }
  return false;
}

static bool ExecFuncFor(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  bool scoped = ForInitNeedsScope(stmt);
  if (scoped) exec.ctx.PushScope();
  ExecFuncForInits(stmt, exec);
  bool returned = ExecFuncForLoop(stmt, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return returned;
}

static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  // A class-typed local (user class, or the built-in `process`/handle types)
  // holds a 64-bit handle and must record its class type so later method calls
  // such as `p.suspend()` dispatch -- module-scope decls do this via
  // TryExecClassVarDecl, but function-body locals take this path instead.
  bool is_class = !type.type_name.empty() && ctx.FindClassType(type.type_name);
  uint32_t w = is_class ? 64 : EvalTypeWidth(type);
  if (w == 0) w = 32;
  auto* v = ctx.CreateLocalVariable(name, w);
  if (is_class) ctx.SetVariableClassType(name, type.type_name);
  if (init) v->value = EvalExpr(init, ctx, arena);
  return v;
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt,
                                     const FuncExecCtx& exec) {
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init,
                     exec.ctx, exec.arena);
}

static void ExecFuncVarDeclStatic(const Stmt* stmt, const FuncExecCtx& exec) {
  auto* existing = exec.ctx.FindStaticFuncVar(exec.func_name, stmt->var_name);
  if (existing) {
    exec.ctx.AliasLocalVariable(stmt->var_name, existing);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, exec.ctx, exec.arena);
  exec.ctx.SaveStaticFuncVar(exec.func_name, stmt->var_name, v);
}

static void ExecFuncVarDecl(const Stmt* stmt, const FuncExecCtx& exec) {
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, exec);
    return;
  }
  if (stmt->var_is_static) {
    ExecFuncVarDeclStatic(stmt, exec);
    return;
  }
  if (exec.ctx.FindLocalVariable(stmt->var_name)) return;
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init,
                     exec.ctx, exec.arena);
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

static bool ExecFuncWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  while (stmt->condition &&
         EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy()) {
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      if (labeled) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncDoWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  do {
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      if (labeled) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  } while (stmt->condition &&
           EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy());
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncForever(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  for (;;) {
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      if (labeled) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

// Resolves the iteration count for a foreach over the named array: the array's
// element count when known, otherwise the bit width of a matching variable.
static uint32_t ResolveForeachSize(std::string_view name, SimContext& ctx) {
  auto* info = ctx.FindArrayInfo(name);
  if (info) return info->size;
  auto* var = ctx.FindVariable(name);
  return var ? var->value.width : 0;
}

// Runs the iteration loop of a foreach over an array of `size` elements,
// pushing a scope that holds the (optional) loop index variable. Returns true
// when the body executed a return.
static bool ExecFuncForeachLoop(const Stmt* stmt, uint32_t size,
                                const FuncExecCtx& exec) {
  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  exec.ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = exec.ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size; ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(exec.arena, 32, i);
    }
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      exec.ctx.PopScope();
      return true;
    }
  }

  exec.ctx.PopScope();
  return false;
}

static bool ExecFuncForeach(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  std::string name = GetForeachArrayName(stmt->expr);
  uint32_t size = name.empty() ? 0 : ResolveForeachSize(name, exec.ctx);
  bool returned = false;
  if (size != 0) {
    returned = ExecFuncForeachLoop(stmt, size, exec);
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return returned;
}

static bool ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr)
        exec.ret_var->value = EvalExpr(stmt->expr, exec.ctx, exec.arena,
                                       exec.ret_var->value.width);
      return true;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, exec.ctx, exec.arena);
      return false;
    case StmtKind::kNonblockingAssign:
      // §13.4.4: a nonblocking assignment is legal in a function body; it
      // schedules into the NBA region just as it does in a process, rather
      // than being dropped. The enclosing call runs inside a process, so the
      // scheduler is active to drain the update.
      ExecNonblockingAssignImpl(stmt, exec.ctx, exec.arena);
      return false;
    case StmtKind::kExprStmt:
      EvalExpr(stmt->expr, exec.ctx, exec.arena);
      return false;
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, exec);
      return false;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, exec);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, exec);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, exec);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, exec);
    case StmtKind::kWhile:
      return ExecFuncWhile(stmt, exec);
    case StmtKind::kDoWhile:
      return ExecFuncDoWhile(stmt, exec);
    case StmtKind::kForever:
      return ExecFuncForever(stmt, exec);
    default:
      return false;
  }
}

void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena) {
  FuncExecCtx exec{ret_var, func->name, ctx, arena};
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, exec)) return;
  }
}

}  // namespace delta
