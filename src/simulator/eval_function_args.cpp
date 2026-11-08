#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/assoc_element.h"
#include "simulator/assoc_index.h"
#include "simulator/class_object.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

bool& CalleeOwnsThisFlag() {
  static thread_local bool flag = false;
  return flag;
}

static bool IsMethodOfObject(const ModuleItem* func, const ClassObject* self) {
  if (self == nullptr) return false;
  for (const ClassTypeInfo* t = self->type; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(func->name));
    if (it != t->methods.end() && it->second == func) return true;
  }
  return false;
}

static bool IsThisOrSuper(const Expr* receiver) {
  return receiver != nullptr && receiver->kind == ExprKind::kIdentifier &&
         (receiver->text == "this" || receiver->text == "super");
}

static bool CalleeOwnsThis(const ModuleItem* func, const Expr* expr,
                           SimContext& ctx) {
  if (func == nullptr || func->is_static_method || expr == nullptr)
    return false;
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || IsThisOrSuper(access->lhs)) {
    return false;
  }
  return IsMethodOfObject(func, ctx.CurrentThis());
}

class CalleeOwnsThisScope {
 public:
  explicit CalleeOwnsThisScope(bool owns) : previous_(CalleeOwnsThisFlag()) {
    CalleeOwnsThisFlag() = owns;
  }
  ~CalleeOwnsThisScope() { CalleeOwnsThisFlag() = previous_; }
  CalleeOwnsThisScope(const CalleeOwnsThisScope&) = delete;
  CalleeOwnsThisScope& operator=(const CalleeOwnsThisScope&) = delete;

 private:
  bool previous_;
};

int ResolveArgIndex(const ModuleItem* func, const Expr* expr,
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

static void RegisterValueArgClassType(const FunctionArg& param,
                                      SimContext& ctx) {
  const DataType& dt =
      *TypeOfThisNamed(&param.data_type, ctx.CurrentMethodClass(), ctx);
  if (!dt.type_name.empty() && ctx.FindClassType(dt.type_name))
    ctx.SetVariableClassType(param.name, dt.type_name);
}

static bool TryBindRefArg(const Expr* expr, int arg_index,
                          std::string_view param_name, SimContext& ctx) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  Variable* target = nullptr;
  {
    CalleeScopeAside aside(ctx);
    target = ctx.FindVariable(IdentifierLookupKey(call_arg));
  }
  if (!target) return false;
  ctx.AliasLocalVariable(param_name, target);
  return true;
}

template <typename Bind>
static void InCalleeScope(SimContext& ctx, Bind bind) {
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  if (!stack.empty()) bind(stack.back());
  ctx.SwapScopeStack(std::move(stack));
}

struct AggregateStorage {
  QueueObject* queue = nullptr;
  AssocArrayObject* assoc = nullptr;
  ArrayInfo* info = nullptr;
  Variable* holder = nullptr;
};

static AggregateStorage FindAggregateStorage(std::string_view name,
                                             SimContext& ctx) {
  CalleeScopeAside aside(ctx);
  AggregateStorage storage;
  storage.queue = ctx.FindQueue(name);
  storage.assoc = ctx.FindAssocArray(name);
  storage.info = ctx.FindArrayInfo(name);
  storage.holder = ctx.FindVariable(name);
  return storage;
}

static void AliasFixedArrayElements(std::string_view actual,
                                    std::string_view formal,
                                    const ArrayInfo& info, SimContext& ctx,
                                    Arena& arena) {
  for (uint32_t j = 0; j < info.size; ++j) {
    auto idx = std::to_string(info.lo + j);
    Variable* src_var = nullptr;
    {
      CalleeScopeAside aside(ctx);
      src_var = ctx.FindVariable(std::string(actual) + "[" + idx + "]");
    }
    if (!src_var) continue;
    auto* dst =
        arena.Create<std::string>(std::string(formal) + "[" + idx + "]");
    ctx.AliasLocalVariable(*dst, src_var);
  }
}

static void AliasAggregateObjects(const AggregateStorage& storage,
                                  std::string_view formal, SimContext& ctx) {
  InCalleeScope(ctx, [&](Scope& frame) {
    if (storage.queue) frame.queues[formal] = storage.queue;
    if (storage.assoc) frame.assoc_arrays[formal] = storage.assoc;
  });
  if (storage.holder) ctx.AliasLocalVariable(formal, storage.holder);
}

static bool TryBindRefQueuePropertyArg(const Expr* call_arg,
                                       const FunctionArg& param,
                                       SimContext& ctx, Arena& arena) {
  if (param.unpacked_dims.empty()) return false;
  AggregateStorage storage;
  {
    CalleeScopeAside aside(ctx);
    storage.queue = FindQueueOfBase(call_arg, ctx, arena);
  }
  if (storage.queue == nullptr) return false;
  AliasAggregateObjects(storage, param.name, ctx);
  return true;
}

static bool TryBindRefAggregateArg(const Expr* call_arg,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (!call_arg) return false;
  if (call_arg->kind == ExprKind::kMemberAccess)
    return TryBindRefQueuePropertyArg(call_arg, param, ctx, arena);
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  std::string actual = IdentifierLookupKey(call_arg);
  AggregateStorage storage = FindAggregateStorage(actual, ctx);
  if (!storage.queue && !storage.assoc && !storage.info)
    return TryBindRefQueuePropertyArg(call_arg, param, ctx, arena);
  if (storage.info && !storage.info->dim_sizes.empty()) return false;
  AliasAggregateObjects(storage, param.name, ctx);
  if (storage.info) {
    ctx.RegisterArrayInScope(param.name, *storage.info);
    if (!storage.queue)
      AliasFixedArrayElements(actual, param.name, *storage.info, ctx, arena);
  }
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
    uint32_t param_width = DeclaredTypeWidth(param.data_type, ctx);
    if (param_width != q->elem_width) return false;
  }

  auto* var = ctx.CreateLocalVariable(param.name, q->elem_width);
  var->value = q->elements[idx];

  if (idx < q->element_ids.size()) {
    ctx.RecordQueueRef({q, q->element_ids[idx], var, call_arg->base->text});
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
      NotifyOwningVar(ctx, b.var_name);
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
  binding.var_name = call_arg->base->text;
  if (aa->is_string_key) {
    binding.str_key = AssocStringKey(EvalExpr(call_arg->index, ctx, arena));
    auto it = aa->str_data.find(binding.str_key);
    if (it == aa->str_data.end()) {
      aa->str_data[binding.str_key] = AssocAllocValue(aa, arena);
      it = aa->str_data.find(binding.str_key);
      NotifyOwningVar(ctx, binding.var_name);
    }
    var->value = it->second;
  } else {
    binding.int_key =
        AssocIntKey(EvalExpr(call_arg->index, ctx, arena), aa->is_wildcard,
                    aa->index_width, aa->is_index_signed);
    auto it = aa->int_data.find(binding.int_key);
    if (it == aa->int_data.end()) {
      aa->int_data[binding.int_key] = AssocAllocValue(aa, arena);
      it = aa->int_data.find(binding.int_key);
      NotifyOwningVar(ctx, binding.var_name);
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
    NotifyOwningVar(ctx, b.var_name);
  }
}

struct ActualValue {
  Logic4Vec value;
  std::string tag;
};

static ActualValue ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                   int arg_index, SimContext& ctx,
                                   Arena& arena) {
  ActualValue resolved;
  if (arg_index >= 0 && expr->args[static_cast<size_t>(arg_index)] != nullptr) {
    CalleeScopeAside aside(ctx);
    const Expr* actual = expr->args[static_cast<size_t>(arg_index)];
    if (TryEvalPatternActual(param, actual, ctx, arena, resolved.value))
      return resolved;
    resolved.value = EvalWithReturnedTag(actual, ctx, arena, resolved.tag);
    return resolved;
  }
  resolved.value = param.default_value
                       ? EvalDefaultInDeclScope(param.default_value, ctx, arena)
                       : MakeLogic4Vec(arena, 32);
  return resolved;
}

static bool TryBindFixedArrayElementRef(const Expr* call_arg,
                                        std::string_view param_name,
                                        SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kSelect) return false;
  if (!call_arg->base || call_arg->base->kind != ExprKind::kIdentifier)
    return false;
  if (!call_arg->index || call_arg->index_end) return false;
  Variable* elem = nullptr;
  {
    CalleeScopeAside aside(ctx);
    if (!ctx.FindArrayInfo(call_arg->base->text)) return false;
    auto idx = EvalExpr(call_arg->index, ctx, arena).ToUint64();
    elem = ctx.FindVariable(std::string(call_arg->base->text) + "[" +
                            std::to_string(idx) + "]");
  }
  if (!elem) return false;
  ctx.AliasLocalVariable(param_name, elem);
  return true;
}

struct ActualArgRef {
  const Expr* expr;
  int index;
  std::string_view result_tag;
};

static void RegisterValueArgStructType(const FunctionArg& param,
                                       const ActualArgRef& ref,
                                       SimContext& ctx);

static bool TryBindRefPropertyArg(const Expr* call_arg,
                                  const FunctionArg& param, SimContext& ctx,
                                  Arena& arena) {
  if (param.is_const || !param.unpacked_dims.empty()) return false;
  ClassObject* obj = nullptr;
  std::string key;
  {
    CalleeScopeAside aside(ctx);
    if (!RefPropertyTarget(call_arg, ctx, arena, obj, key)) return false;
  }
  Variable* cell = obj->AcquireRefCell(key, arena);
  cell->is_4state = DeclaredTypeIs4State(param.data_type, ctx);
  cell->is_signed = DeclaredTypeIsSigned(param.data_type, ctx);
  ctx.AliasLocalVariable(param.name, cell);
  RegisterValueArgClassType(param, ctx);
  return true;
}

static bool TryBindRefDirectionArg(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index >= 0 &&
      TryBindRefAggregateArg(expr->args[static_cast<size_t>(arg_index)], param,
                             ctx, arena)) {
    return true;
  }
  if (arg_index >= 0 &&
      TryBindRefPropertyArg(expr->args[static_cast<size_t>(arg_index)], param,
                            ctx, arena)) {
    return true;
  }
  if (TryBindRefArg(expr, arg_index, param.name, ctx)) {
    RegisterValueArgStructType(param, {expr, arg_index, {}}, ctx);
    RegisterValueArgClassType(param, ctx);
    if (param.unpacked_dims.empty())
      RecordVariableEnumType(param.name, param.data_type, ctx);
    return true;
  }
  if (TryBindQueueElementRef(expr, arg_index, param, ctx, arena)) return true;
  if (TryBindAssocElementRef(expr, arg_index, param, ctx, arena)) return true;
  if (arg_index >= 0 &&
      TryBindFixedArrayElementRef(expr->args[static_cast<size_t>(arg_index)],
                                  param.name, ctx, arena)) {
    RegisterValueArgClassType(param, ctx);
    return true;
  }
  return false;
}

static std::string ActualTag(const FunctionArg& param, const Expr* actual,
                             const ActualArgRef& ref, SimContext& ctx) {
  if (actual == nullptr || param.direction == Direction::kOutput) return {};
  if (actual->kind != ExprKind::kIdentifier) return std::string(ref.result_tag);
  CalleeScopeAside aside(ctx);
  std::string key = TagKeyOfName(DeclaredKindsKey(actual), ctx);
  return std::string(ctx.GetVariableTag(key));
}

static bool TryBindIdentifierActualLayout(const FunctionArg& param,
                                          const Expr* actual, SimContext& ctx) {
  if (actual == nullptr || actual->kind != ExprKind::kIdentifier) return false;
  const StructTypeInfo* sinfo = nullptr;
  {
    CalleeScopeAside aside(ctx);
    sinfo = StructLayoutOfName(DeclaredKindsKey(actual), ctx);
  }
  if (sinfo == nullptr) return false;
  StructTypeInfo copy = *sinfo;
  ctx.RegisterStructType(param.name, copy);
  ctx.SetVariableStructType(param.name, param.name);
  return true;
}

static void RegisterValueArgStructType(const FunctionArg& param,
                                       const ActualArgRef& ref,
                                       SimContext& ctx) {
  const Expr* actual = (ref.index >= 0)
                           ? ref.expr->args[static_cast<size_t>(ref.index)]
                           : nullptr;
  if (actual && TryBindTaggedActual(param, actual, ctx)) return;
  if (!TryBindInlineAggregateFormal(param, ctx) &&
      !TryBindIdentifierActualLayout(param, actual, ctx) &&
      !TryBindNamedAggregateFormal(param, ctx)) {
    return;
  }
  const StructTypeInfo* layout = ctx.GetVariableStructType(param.name);
  if (layout == nullptr || !layout->is_union) return;
  ctx.SetVariableTag(param.name, ActualTag(param, actual, ref, ctx));
}

static const Expr* ActualExprOf(const ActualArgRef& ref) {
  if (ref.index < 0) return nullptr;
  return ref.expr->args[static_cast<size_t>(ref.index)];
}

static bool TryReuseStaticFormal(const FunctionArg& param,
                                 const ActualArgRef& actual,
                                 const Logic4Vec& val, const ModuleItem* func,
                                 SimContext& ctx) {
  if (!func || !func->is_static || func->is_automatic) return false;
  auto* existing = ctx.FindStaticFuncVar(func->name, param.name);
  if (existing == nullptr) return false;
  ctx.AliasLocalVariable(param.name, existing);
  if (param.direction != Direction::kOutput) {
    existing->value = val;
    if (!existing->is_4state) CoerceTo2State(existing->value);
  }
  RegisterValueArgStructType(param, actual, ctx);
  RegisterValueArgClassType(param, ctx);
  return true;
}

static bool DeclaredKindIsIntegral(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

static Logic4Vec ConvertToFormalType(Logic4Vec val, const DataType& dt,
                                     uint32_t formal_width, SimContext& ctx,
                                     Arena& arena) {
  if (formal_width == 0) return val;
  if (val.is_real && DeclaredKindIsIntegral(dt.kind))
    return ConvertRealForKnownLhs(val, false, formal_width, arena);
  if (DeclaredTypeIsReal(dt, ctx))
    return ConvertRealForKnownLhs(val, true, formal_width, arena);
  if (formal_width != val.width) return ResizeToWidth(val, formal_width, arena);
  return val;
}

static void BindValueArg(const FunctionArg& param, const ActualArgRef& actual,
                         const ModuleItem* func, SimContext& ctx,
                         Arena& arena) {
  const Expr* expr = actual.expr;
  int arg_index = actual.index;
  ActualValue resolved = ResolveArgValue(param, expr, arg_index, ctx, arena);
  auto val = OwnRhsWords(resolved.value, arena);
  ActualArgRef bound{expr, arg_index, resolved.tag};
  const auto& dt = param.data_type;
  if (dt.kind != DataTypeKind::kImplicit) {
    val = ConvertToFormalType(val, dt, EvalFormalArgWidth(dt, ctx, arena), ctx,
                              arena);
  }
  if (param.direction == Direction::kOutput)
    val = OutputFormalDefault(dt, val.width, ctx, arena);

  bool is_static_sub = func && func->is_static && !func->is_automatic;
  SyncHandle sync = SyncActualOf(param, ActualExprOf(bound), func, ctx, arena);
  if (TryReuseStaticFormal(param, bound, val, func, ctx)) {
    BindSyncFormal(sync, ctx.FindLocalVariable(param.name), ctx);
    return;
  }

  auto* var = ctx.CreateLocalVariable(
      param.name, val.width, DeclaredTypeIsSigned(param.data_type, ctx));
  var->is_4state = DeclaredTypeIs4State(param.data_type, ctx);
  var->declared_type = &param.data_type;
  var->is_string = DeclaredTypeIsString(dt, ctx);
  var->is_real = DeclaredTypeIsReal(dt, ctx);
  if (param.unpacked_dims.empty()) RecordVariableEnumType(param.name, dt, ctx);
  var->is_virtual_interface = DeclaresAVirtualInterface(dt, ctx);
  var->is_event = dt.kind == DataTypeKind::kEvent;
  var->value = val;
  var->value.is_signed = var->is_signed;
  if (!var->is_4state) CoerceTo2State(var->value);
  if (is_static_sub) ctx.SaveStaticFuncVar(func->name, param.name, var);
  RegisterValueArgStructType(param, bound, ctx);
  RegisterValueArgClassType(param, ctx);
  BindSyncFormal(sync, var, ctx);
}

void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  CalleeOwnsThisScope owns_this(CalleeOwnsThis(func, expr, ctx));
  CalleeOwnsClassScope owns_class(func->is_static_method);
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    int ai = ResolveArgIndex(func, expr, i);
    const auto& param = func->func_args[i];
    if (param.direction == Direction::kRef &&
        TryBindRefDirectionArg(expr, ai, param, ctx, arena)) {
      BindRefSyncFormal(param,
                        ai >= 0 ? expr->args[static_cast<size_t>(ai)] : nullptr,
                        func, ctx, arena);
      continue;
    }
    if (TryBindEventFormal(expr, ai, param, ctx)) continue;
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)], param,
                                   ctx, arena)) {
      KeepStaticArrayFormal(func, param, ctx, arena);
      continue;
    }
    BindValueArg(param, {expr, ai, {}}, func, ctx, arena);
  }
}

}  // namespace delta
