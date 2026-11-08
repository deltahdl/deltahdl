#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static const Expr* SelectRoot(const Expr* actual) {
  while (actual && actual->kind == ExprKind::kSelect) actual = actual->base;
  return actual;
}

static bool CopiesOutOnReturn(const FunctionArg& formal, const Expr* actual) {
  if (formal.direction == Direction::kOutput ||
      formal.direction == Direction::kInout) {
    return true;
  }
  if (formal.direction != Direction::kRef || formal.is_const) return false;
  if (!formal.unpacked_dims.empty()) return false;
  const Expr* root = SelectRoot(actual);
  return root != nullptr && root->kind == ExprKind::kMemberAccess;
}

struct ElementWriteback {
  std::string target;
  Logic4Vec value;
};

struct AggregateWriteback {
  const Expr* actual = nullptr;
  const AssocArrayObject* assoc = nullptr;
  const QueueObject* queue = nullptr;
  std::vector<Logic4Vec> elements;
};

struct TagWriteback {
  std::string_view actual;
  std::string tag;
};

struct CallerWrites {
  std::vector<std::pair<const Expr*, Logic4Vec>> values;
  std::vector<ElementWriteback> elements;
  std::vector<TagWriteback> tags;
  std::vector<AggregateWriteback> aggregates;
  bool Empty() const {
    return values.empty() && elements.empty() && tags.empty() &&
           aggregates.empty();
  }
};

template <typename Read>
static void WithCalleeScopeOff(SimContext& ctx, Read read) {
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  Scope callee = std::move(stack.back());
  stack.pop_back();
  ctx.SwapScopeStack(std::move(stack));
  read();
  stack = ctx.SwapScopeStack({});
  stack.push_back(std::move(callee));
  ctx.SwapScopeStack(std::move(stack));
}

static bool TakesElementsByPosition(const Expr* actual, SimContext& ctx,
                                    const ArrayInfo*& actual_info) {
  actual_info = nullptr;
  if (actual->kind == ExprKind::kMemberAccess) return true;
  bool by_position = false;
  WithCalleeScopeOff(ctx, [&] {
    actual_info = ctx.FindArrayInfo(actual->text);
    by_position =
        actual_info == nullptr || ctx.FindQueue(actual->text) != nullptr;
  });
  return by_position;
}

static void CollectElementWritebacks(const FunctionArg& formal,
                                     const Expr* actual, SimContext& ctx,
                                     Arena& arena, CallerWrites& out) {
  if (formal.unpacked_dims.empty() || actual == nullptr ||
      (actual->kind != ExprKind::kIdentifier &&
       actual->kind != ExprKind::kMemberAccess)) {
    return;
  }
  const ArrayInfo* info = ctx.FindArrayInfo(formal.name);
  if (info == nullptr) return;
  const ArrayInfo* actual_info = nullptr;
  bool by_position = TakesElementsByPosition(actual, ctx, actual_info);
  bool same_sizes = actual_info != nullptr && actual_info->size == info->size &&
                    actual_info->dim_sizes == info->dim_sizes;
  const ArrayInfo& target = same_sizes ? *actual_info : *info;
  AggregateWriteback to_queue;
  to_queue.actual = actual;
  uint32_t count = ArrayElementCount(*info);
  for (uint32_t k = 0; k < count; ++k) {
    auto* elem = ctx.FindLocalVariable(std::string(formal.name) +
                                       ArrayElementSuffixAt(*info, k));
    if (elem == nullptr) continue;
    Logic4Vec value = OwnRhsWords(elem->value, arena);
    if (by_position) {
      to_queue.elements.push_back(value);
      continue;
    }
    out.elements.push_back(
        {std::string(actual->text) + ArrayElementSuffixAt(target, k), value});
  }
  if (by_position) out.aggregates.push_back(std::move(to_queue));
}

static bool CollectAggregateWriteback(const FunctionArg& formal,
                                      const Expr* actual, SimContext& ctx,
                                      std::vector<AggregateWriteback>& out) {
  if (formal.unpacked_dims.empty() || actual == nullptr) return false;
  AggregateWriteback write;
  write.actual = actual;
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  if (!stack.empty()) {
    const Scope& callee = stack.back();
    if (auto it = callee.queues.find(formal.name); it != callee.queues.end())
      write.queue = it->second;
    auto it = callee.assoc_arrays.find(formal.name);
    if (it != callee.assoc_arrays.end()) write.assoc = it->second;
  }
  ctx.SwapScopeStack(std::move(stack));
  if (write.queue == nullptr && write.assoc == nullptr) return false;
  out.push_back(std::move(write));
  return true;
}

static void AssignClassArray(const Expr* actual,
                             const std::vector<Logic4Vec>& src, SimContext& ctx,
                             Arena& arena) {
  ClassArrayRef ref;
  if (!ResolveClassArray(actual, ctx, arena, ref)) return;
  if (ref.prop->is_dynamic) {
    ResizeClassArray(ref, static_cast<uint32_t>(src.size()), nullptr, ctx,
                     arena);
    ref.size = static_cast<uint32_t>(src.size());
  }
  ArrayInfo shape = ClassArrayShape(ref);
  for (uint32_t k = 0; k < shape.size && k < src.size(); ++k)
    StoreClassArrayElement(ref, ElementIndexAt(shape, k), src[k], ctx, arena);
}

static void AssignAggregate(const AggregateWriteback& write, SimContext& ctx,
                            Arena& arena) {
  ClassObject* owner = nullptr;
  if (write.assoc != nullptr) {
    auto* dst = FindAssocArrayOfBase(write.actual, ctx, arena, &owner);
    if (dst == nullptr) return;
    dst->int_data.clear();
    dst->str_data.clear();
    for (const auto& [key, val] : write.assoc->int_data)
      dst->int_data[key] = OwnRhsWords(val, arena);
    for (const auto& [key, val] : write.assoc->str_data)
      dst->str_data[key] = OwnRhsWords(val, arena);
    if (owner != nullptr) {
      ctx.NotifyClassHandleWatchers(owner->handle);
    } else if (write.actual->kind == ExprKind::kIdentifier) {
      NotifyOwningVar(ctx, DeclaredKindsKey(write.actual));
    }
    return;
  }
  const std::vector<Logic4Vec>& src =
      write.queue != nullptr ? write.queue->elements : write.elements;
  auto* dst = FindQueueOfBase(write.actual, ctx, arena, &owner);
  if (dst == nullptr) {
    AssignClassArray(write.actual, src, ctx, arena);
    return;
  }
  std::vector<Logic4Vec> copy;
  copy.reserve(src.size());
  for (const auto& elem : src) copy.push_back(OwnRhsWords(elem, arena));
  dst->elements = std::move(copy);
  dst->AssignFreshIds();
  AnnounceQueueChange(write.actual, owner, ctx);
}

static bool CarriesTagOut(const FunctionArg& formal) {
  if (formal.direction == Direction::kOutput ||
      formal.direction == Direction::kInout) {
    return true;
  }
  return formal.direction == Direction::kRef && !formal.is_const;
}

static void CollectTagWriteback(const FunctionArg& formal, const Expr* actual,
                                SimContext& ctx,
                                std::vector<TagWriteback>& out) {
  if (!CarriesTagOut(formal) || actual == nullptr ||
      actual->kind != ExprKind::kIdentifier) {
    return;
  }
  const StructTypeInfo* layout = ctx.GetVariableStructType(formal.name);
  if (layout == nullptr || !layout->is_union) return;
  out.push_back({actual->text, std::string(ctx.GetVariableTag(formal.name))});
}

static void AssignInCallerScope(const CallerWrites& writes, SimContext& ctx,
                                Arena& arena) {
  WithCalleeScopeOff(ctx, [&] {
    for (const auto& [target, value] : writes.values) {
      PerformBlockingAssign(target, value, ctx, arena);
    }
    for (const auto& [target, value] : writes.elements) {
      if (auto* elem = ctx.FindVariable(target)) WriteVar(elem, value, arena);
    }
    for (const auto& [actual, tag] : writes.tags) {
      ctx.SetVariableTag(*arena.Create<std::string>(TagKeyOfName(actual, ctx)),
                         tag);
    }
    for (const auto& write : writes.aggregates)
      AssignAggregate(write, ctx, arena);
  });
}

static void ReleaseRefPropertyCells(const ModuleItem* func, const Expr* expr,
                                    SimContext& ctx, Arena& arena) {
  std::vector<const Expr*> actuals;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const FunctionArg& formal = func->func_args[i];
    int ai = ResolveArgIndex(func, expr, i);
    if (formal.direction == Direction::kRef && !formal.is_const && ai >= 0 &&
        formal.unpacked_dims.empty()) {
      actuals.push_back(expr->args[static_cast<size_t>(ai)]);
    }
  }
  if (actuals.empty()) return;
  WithCalleeScopeOff(ctx, [&] {
    for (const Expr* actual : actuals) {
      ClassObject* obj = nullptr;
      std::string key;
      if (RefPropertyTarget(actual, ctx, arena, obj, key))
        obj->ReleaseRefCell(key);
    }
  });
}

Logic4Vec EvalDefaultInDeclScope(const Expr* default_value, SimContext& ctx,
                                 Arena& arena) {
  std::optional<InstancePrefixOverride> in_callee;
  if (const Process* proc = ctx.CurrentProcess()) {
    in_callee.emplace(ctx.InstancePrefixOverride(), proc->inst_prefix);
  }
  return EvalExpr(default_value, ctx, arena);
}

static bool TryWritebackEventFormal(const FunctionArg& formal,
                                    const Expr* actual, Variable* local,
                                    SimContext& ctx) {
  if (formal.data_type.kind != DataTypeKind::kEvent || actual == nullptr ||
      actual->kind != ExprKind::kIdentifier || !local->is_event) {
    return false;
  }
  CalleeScopeAside aside(ctx);
  if (ctx.FindLocalVariable(actual->text) != nullptr) {
    ctx.AliasLocalVariable(actual->text, local);
  } else {
    ctx.AliasVariable(actual->text, local);
  }
  return true;
}

static void CollectValueWriteback(const FunctionArg& formal, const Expr* actual,
                                  const Logic4Vec& value, CallerWrites& writes,
                                  CallerWrites& default_writes) {
  if (actual != nullptr) {
    writes.values.emplace_back(actual, value);
  } else if (formal.default_value != nullptr) {
    default_writes.values.emplace_back(formal.default_value, value);
  }
}

void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena) {
  CallerWrites writes;
  CallerWrites default_writes;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const FunctionArg& formal = func->func_args[i];
    int ai = ResolveArgIndex(func, expr, i);
    const Expr* actual =
        ai >= 0 ? expr->args[static_cast<size_t>(ai)] : nullptr;
    CollectTagWriteback(formal, actual, ctx, writes.tags);
    if (!CopiesOutOnReturn(formal, actual)) continue;
    if (CollectAggregateWriteback(formal, actual, ctx, writes.aggregates))
      continue;
    auto* local = ctx.FindLocalVariable(formal.name);
    if (!local) {
      CollectElementWritebacks(formal, actual, ctx, arena, writes);
      continue;
    }
    if (TryWritebackEventFormal(formal, actual, local, ctx)) continue;
    CollectValueWriteback(formal, actual, local->value, writes, default_writes);
  }
  if (!writes.Empty()) AssignInCallerScope(writes, ctx, arena);
  ReleaseRefPropertyCells(func, expr, ctx, arena);
  if (default_writes.Empty()) return;
  std::optional<InstancePrefixOverride> in_callee;
  if (const Process* proc = ctx.CurrentProcess()) {
    in_callee.emplace(ctx.InstancePrefixOverride(), proc->inst_prefix);
  }
  AssignInCallerScope(default_writes, ctx, arena);
}

}  // namespace delta
