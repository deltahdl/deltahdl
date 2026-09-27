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

// The root an actual is written on: the base of a select chain, else the
// actual itself.
static const Expr* SelectRoot(const Expr* actual) {
  while (actual && actual->kind == ExprKind::kSelect) actual = actual->base;
  return actual;
}

// Whether the formal's value is carried back into the actual when the
// subroutine returns. §13.5.2 (printed page 349) has an output or inout formal
// copied to its actual then, and lists a class property and a member of an
// unpacked structure among what may be passed by reference. Neither of those
// is a variable of its own -- a property is a field of its object and a
// member a window of the structure's variable -- so there is nothing for the
// ref binds to alias and the formal took BindValueArg's copy: `add(s.b, 20)`
// and `add(h.v, 5)` left 5 and 60 standing. The copy is carried back into the
// member or property here, through the assignment the actual takes as a
// target, exactly as a queue or associative-array element's is by
// WritebackQueueRefs and WritebackAssocRefs. A ref actual rooted anywhere
// else is either aliased, and needs no copy-out, or is no target at all; a
// const ref formal (printed page 350) is read only.
static bool CopiesOutOnReturn(const FunctionArg& formal, const Expr* actual) {
  if (formal.direction == Direction::kOutput ||
      formal.direction == Direction::kInout) {
    return true;
  }
  if (formal.direction != Direction::kRef || formal.is_const) return false;
  // A formal declared with unpacked dimensions is an aggregate, which the
  // copy BindValueArg makes of a member or property does not stand for.
  if (!formal.unpacked_dims.empty()) return false;
  const Expr* root = SelectRoot(actual);
  return root != nullptr && root->kind == ExprKind::kMemberAccess;
}

// One element of an output or inout formal declared with an unpacked
// dimension, and the caller's element variable it is copied into.
struct ElementWriteback {
  std::string target;
  Logic4Vec value;
};

// An output or inout array formal whose contents go back to an actual that
// holds its elements in an object rather than in variables: the formal's own
// associative array or queue, or, for a fixed-size formal bound to a dynamic
// array or queue, its element values from the left.
struct AggregateWriteback {
  const Expr* actual = nullptr;
  const AssocArrayObject* assoc = nullptr;
  const QueueObject* queue = nullptr;
  std::vector<Logic4Vec> elements;
};

// The tag an output, inout or ref formal of tagged union type holds when the
// subroutine returns, and the actual it is carried back to.
struct TagWriteback {
  std::string_view actual;
  std::string tag;
};

// Everything a return copies into the caller: whole actuals assigned as
// targets, element variables, union tags and aggregates.
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

// Runs `read` with the callee's scope, the top of the stack, taken off and put
// back after, so a name the caller wrote is read as the caller's.
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

// §13.3 (printed page 337) writes mytask4's `output [3:0][7:0] y[1:0]`, a
// formal with an unpacked dimension, and §13.5 (printed page 348) has the
// return pass the values of the output and inout formals to the variables of
// the call. TryBindArrayArg materializes such a formal as one variable per
// element, `yo[0]` and `yo[1]`, with the shape recorded in the callee's scope
// and no variable of the formal's own name -- which was the one name the
// copy-out looked up, so every element of the actual kept its x. The elements
// are gathered here, while the callee's scope still holds the shape and the
// element variables; the actual is the identifier TryBindArrayArg bound the
// formal from, whose elements are the `y[idx]` variables CreateArrayElements
// (lowerer_var.cpp) declares. Each value takes its own words, as the copy in
// did: the formal's variable goes with the call, and the caller's element is
// what keeps the value.
//
// §7.7 (printed page 162) lets the actual have another range than the
// formal, or be a dynamic array or queue, and §7.6 pairs the elements left to
// right, so the formal's k-th element from the left goes to the actual's
// k-th: to the element variable at that position of the actual's own bounds,
// or into the actual's queue (AggregateWriteback::elements).
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
  // An actual that is no declared fixed-size array -- a queue, or a property
  // reached through a handle or by its bare name in a method, which holds its
  // elements on the object -- takes them back by position (AssignAggregate).
  bool actual_is_queue = actual->kind == ExprKind::kMemberAccess;
  WithCalleeScopeOff(ctx, [&] {
    if (actual_is_queue) return;
    actual_info = ctx.FindArrayInfo(actual->text);
    actual_is_queue =
        actual_info == nullptr || ctx.FindQueue(actual->text) != nullptr;
  });
  AggregateWriteback to_queue{.actual = actual};
  for (uint32_t k = 0; k < info->size; ++k) {
    std::string suffix = "[" + std::to_string(ElementIndexAt(*info, k)) + "]";
    auto* elem = ctx.FindLocalVariable(std::string(formal.name) + suffix);
    if (elem == nullptr) continue;
    Logic4Vec value = OwnRhsWords(elem->value, arena);
    if (actual_is_queue) {
      to_queue.elements.push_back(value);
      continue;
    }
    uint32_t idx = (actual_info != nullptr && actual_info->size == info->size)
                       ? ElementIndexAt(*actual_info, k)
                       : ElementIndexAt(*info, k);
    out.elements.push_back(
        {std::string(actual->text) + "[" + std::to_string(idx) + "]", value});
  }
  if (actual_is_queue) out.aggregates.push_back(std::move(to_queue));
}

// §7.7 (printed page 162) makes the rules of array argument passing by value
// "the same as for array assignment", and §13.5 (printed 348) copies an
// output or inout formal to its actual on return, so a dynamic array, queue or
// associative array formal goes back whole: `mk(d)` with `output int arr[]`
// sized by `new[3]` leaves d of size 3. Such a formal holds its elements in the
// callee frame's own QueueObject or AssocArrayObject rather than in a variable
// of its name, so the copy-out found no variable and nothing reached the
// actual. Only the callee's own frame is read, so an actual named like the
// formal is not taken for it. False where the formal holds no such object.
static bool CollectAggregateWriteback(const FunctionArg& formal,
                                      const Expr* actual, SimContext& ctx,
                                      std::vector<AggregateWriteback>& out) {
  if (formal.unpacked_dims.empty() || actual == nullptr) return false;
  AggregateWriteback write{.actual = actual};
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

// §7.6 (printed page 160) assigns an array to a fixed or dynamic array
// property element by element from the left, a dynamic one first resized to
// the source's size (§7.5.1); a fixed one takes as many as it holds. An
// actual that names no such property keeps what it held.
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

// Replaces the contents of the associative array or queue the actual names,
// in the caller's scope, with the formal's, each element taking its own words,
// and tells §9.4.2's watchers of the actual that it changed. An actual that
// names neither keeps what it held.
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

// §7.3.2 (printed page 151): a tagged union's value is its tag beside the
// member value, so the value §13.5 (printed 348) passes from an output or
// inout formal to the caller's variable on return carries the tag: after
// `retag(u)` with `output u_t o` assigned `tagged Valid 4` inside, the actual
// holds Valid. The bits alone were copied out, so `u.Valid` of the caller was
// reported against the tag the actual held before the call. A ref formal
// aliases the actual's variable but not its tag entry -- TagKeyOfName answers
// the formal's bare name for a local, the alias included -- so a retag
// through a non-const ref formal is carried back the same way. The formal's
// tag stands under its bare name, the key the bind wrote it by
// (CopyUnionTagIn in eval_function_args.cpp), and only a formal with a union
// layout on file has one to carry.
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

// The actual is an expression of the caller's, so it is assigned with the
// callee's scope, the top of the stack at this point, taken off the stack and
// put back after: an actual spelled like the formal would otherwise resolve
// to the formal and the caller's variable never change. An element of an
// array actual is a variable of the caller's, named rather than written as an
// expression, and is stored into as §11.4.1's compound operators store into a
// variable: sized to it, coerced where it is 2-state, declined while it is
// forced, its watchers told. A tag is recorded under the key the actual's
// storage was created by, resolved in the caller's scope as the value's
// target is (TagKeyOfName), and the key is interned in the arena: the tag
// table keeps the view it is given, and a key that went with this call
// would be read against freed memory by every later access of the actual.
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

// §13.5.2: an output or inout formal is copied to its actual when the
// subroutine returns, and so is a ref formal bound to a member or property
// (CopiesOutOnReturn). A formal with no variable of its own name is one
// TryBindArrayArg spread over per-element variables, copied out element by
// element (CollectElementWritebacks). A tagged union formal's tag goes back
// with its value (CollectTagWriteback), before CopiesOutOnReturn declines the
// aliased ref formal whose tag entry is its own.
Logic4Vec EvalDefaultInDeclScope(const Expr* default_value, SimContext& ctx,
                                 Arena& arena) {
  std::optional<InstancePrefixOverride> in_callee;
  if (const Process* proc = ctx.CurrentProcess()) {
    in_callee.emplace(ctx.InstancePrefixOverride(), proc->inst_prefix);
  }
  return EvalExpr(default_value, ctx, arena);
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
    if (actual != nullptr) {
      writes.values.emplace_back(actual, local->value);
    } else if (formal.default_value != nullptr) {
      default_writes.values.emplace_back(formal.default_value, local->value);
    }
  }
  if (!writes.Empty()) AssignInCallerScope(writes, ctx, arena);
  if (default_writes.Empty()) return;
  // §13.5.3: a default names its target in the scope of the declaration, the
  // instance the process stands in for the call, not the caller's.
  std::optional<InstancePrefixOverride> in_callee;
  if (const Process* proc = ctx.CurrentProcess()) {
    in_callee.emplace(ctx.InstancePrefixOverride(), proc->inst_prefix);
  }
  AssignInCallerScope(default_writes, ctx, arena);
}

}  // namespace delta
