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
#include "simulator/stmt_exec.h"

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
// `loc` is where the actual was written, which the size-mismatch report names;
// the formal carries no position of its own.
static bool BindQueueToFixedFormal(QueueObject* src_q,
                                   const FunctionArg& formal, SimContext& ctx,
                                   Arena& arena, SourceLoc loc) {
  // A fixed-size formal accepts a dynamic array or queue only when the
  // sizes are equal; this can only be verified at the time of the call.
  auto formal_size = EvalExpr(formal.unpacked_dims[0], ctx, arena).ToUint64();
  if (src_q->elements.size() != formal_size) {
    ctx.GetDiag().Error(
        loc,
        "array size mismatch: formal expects " + std::to_string(formal_size) +
            " elements, actual has " + std::to_string(src_q->elements.size()),
        Subclause::Unread());
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
                            SimContext& ctx, Arena& arena, SourceLoc loc) {
  if (formal.unpacked_dims.empty()) return false;
  if (formal.unpacked_dims[0] != nullptr) {
    return BindQueueToFixedFormal(src_q, formal, ctx, arena, loc);
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
    return TryBindQueueArg(src_q, formal, ctx, arena, call_arg->range.start);
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

// §8.14: a class-typed formal holds a handle whose DECLARED type governs
// non-virtual member and property resolution. Record it just as a local class
// variable does (see CreateFuncLocalVar in eval_function_body.cpp); otherwise
// a base-typed formal bound
// to a derived actual would have no declared type on file and member lookup
// would fall back to the runtime object's type, wrongly reaching the derived
// override instead of the hidden base member.
static void RegisterValueArgClassType(const FunctionArg& param,
                                      SimContext& ctx) {
  const auto& dt = param.data_type;
  if (!dt.type_name.empty() && ctx.FindClassType(dt.type_name))
    ctx.SetVariableClassType(param.name, dt.type_name);
}

// §13.5: the actual argument a formal is bound from -- the call expression and
// the position the actual occupies in its argument list (negative when the call
// supplies none, so the formal takes its default).
struct ActualArgRef {
  const Expr* expr;
  int index;
};

static void BindValueArg(const FunctionArg& param, const ActualArgRef& actual,
                         const ModuleItem* func, SimContext& ctx,
                         Arena& arena) {
  const Expr* expr = actual.expr;
  int arg_index = actual.index;
  auto val = ResolveArgValue(param, expr, arg_index, ctx, arena);
  const auto& dt = param.data_type;
  if (dt.kind != DataTypeKind::kImplicit) {
    uint32_t formal_width = EvalFormalArgWidth(dt, ctx, arena);
    if (formal_width > 0 && formal_width != val.width)
      val = ResizeToWidth(val, formal_width, arena);
  }
  // 13.3.2/13.5.1: an output formal is not passed a value from the caller; only
  // input and inout formals receive the actual's value. The actual is evaluated
  // above solely to size the formal - reset the bits to the default so a
  // read-before-write (and, for an automatic task, each fresh entry) observes
  // the default value rather than the caller's current value.
  if (param.direction == Direction::kOutput)
    val = MakeLogic4VecVal(arena, val.width, 0);

  // §13.3.2: the arguments of a static task/function are static storage that
  // retains its value between invocations. On a later call the formal already
  // exists in the static-frame store, so reuse that cell instead of a fresh
  // default-initialized one: an input/inout formal is refreshed with the value
  // just passed, while an output formal keeps whatever it retained from the
  // last call (a read-before-write sees the retained value, not the default).
  // An automatic task takes the fresh-each-entry path below, per §13.3.2 /
  // Claim E.
  bool is_static_sub = func && func->is_static && !func->is_automatic;
  if (is_static_sub) {
    auto* existing = ctx.FindStaticFuncVar(func->name, param.name);
    if (existing) {
      ctx.AliasLocalVariable(param.name, existing);
      if (param.direction != Direction::kOutput) existing->value = val;
      RegisterValueArgStructType(param, expr, arg_index, ctx);
      RegisterValueArgClassType(param, ctx);
      return;
    }
  }

  auto* var = ctx.CreateLocalVariable(param.name, val.width);
  var->value = val;
  if (is_static_sub) ctx.SaveStaticFuncVar(func->name, param.name, var);
  // A named-type struct formal (input s_t arg) has kind kNamed, not kStruct, so
  // resolve from the actual argument unconditionally; the resolver is a no-op
  // for non-struct actuals.
  RegisterValueArgStructType(param, expr, arg_index, ctx);
  RegisterValueArgClassType(param, ctx);
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
    BindValueArg(param, {expr, ai}, func, ctx, arena);
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
}  // namespace delta
