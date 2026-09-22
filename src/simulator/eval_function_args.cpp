#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/virtual_interface.h"

namespace delta {

// The flag CalleeScopeAside reads (eval_function_args_internal.h): whether
// the object on top of the `this` stack is the callee's own, which
// BindFunctionArgs decides (CalleeOwnsThis) for one binding at a time
// (CalleeOwnsThisScope).
bool& CalleeOwnsThisFlag() {
  static thread_local bool flag = false;
  return flag;
}

// Whether the object on top of the `this` stack is the callee's own, pushed
// for the call being bound rather than the caller's: the call is written on a
// receiver, `h.m(...)`, and `func` is a non-static method of that object's
// class or of one it inherits from. A call through `this` or `super` runs on
// the caller's own object, and a static method (§8.10) is run with no object
// pushed, so neither has anything to set aside; a hierarchical call written
// `inst.f(...)` has a receiver but names no method of the object, so the
// object on top is the caller's and stays. A constructor's actuals are bound
// by EvalClassNew with the object under construction already popped, and
// its `super.new(...)` and extends-specifier actuals carry no receiver.
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

// Holds CalleeOwnsThisFlag at the answer for one binding and restores the
// enclosing binding's on the way out: an actual that is itself a method call
// binds that call's actuals with the caller's object already set aside.
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

// §8.14: a class-typed formal holds a handle whose DECLARED type governs
// non-virtual member and property resolution. Record it just as a local class
// variable does (see CreateFuncLocalVar in eval_function_body.cpp); otherwise
// a base-typed formal bound
// to a derived actual would have no declared type on file and member lookup
// would fall back to the runtime object's type, wrongly reaching the derived
// override instead of the hidden base member.
//
// A ref formal is recorded the same way. §8.2 lets an object be declared as a
// ref argument, the handle being what is passed, and §13.5.2 makes the formal
// a reference to the caller's variable; TryClassNewAssign constructs for
// `r = new` only when the target's name has a declared class type on file, so
// a `ref C r` bound with no record fell to the generic evaluation, which reads
// a bare `new` as a null handle -- the caller's variable stayed null after
// `remake(b, 62)` while `ref int cnt` beside it counted.
static void RegisterValueArgClassType(const FunctionArg& param,
                                      SimContext& ctx) {
  const auto& dt = param.data_type;
  if (!dt.type_name.empty() && ctx.FindClassType(dt.type_name))
    ctx.SetVariableClassType(param.name, dt.type_name);
}

// §13.5.2 (printed page 349) with §3.12.1 (printed 56): the actual is the
// variable its key names (IdentifierLookupKey), `$unit::g` the unit's own.
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

// Runs `bind` on the callee's scope, the top frame of the stack, with the
// stack taken off the context for the duration and put back after. SimContext
// registers a declaration of the innermost scope only through CreateQueue and
// CreateAssocArray, each of which makes a new object; a ref formal needs the
// frame to name the caller's own.
template <typename Bind>
static void InCalleeScope(SimContext& ctx, Bind bind) {
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  if (!stack.empty()) bind(stack.back());
  ctx.SwapScopeStack(std::move(stack));
}

// The storage a declared aggregate's name stands for in the caller: the
// QueueObject of a queue or dynamic array, the AssocArrayObject of an
// associative array, the shape of a fixed-size array, and the whole variable
// Lowerer::LowerVar declares under the name before LowerVarAggregate gives
// the aggregate any of these. Read with the callee's scope set aside, as
// TryBindRefArg reads the actual, so a formal of the last call to a static
// subroutine never answers for the caller's aggregate.
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

// Makes each element of the formal, `a[idx]` for every index of the shape,
// the caller's element variable `arr[idx]`, which is how TryArrayElementSelect
// and the select assignment reach an element of a fixed-size array. The
// elements are read with the callee's scope set aside and the aliases made
// with it back on top, one element at a time; the formal's names are interned
// in the arena, which outlives the scope they are keys of.
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

// Makes `formal` name, in the callee's scope, the objects the actual's name
// stands for in the caller's: its QueueObject, its AssocArrayObject and the
// whole variable declared under the name.
static void AliasAggregateObjects(const AggregateStorage& storage,
                                  std::string_view formal, SimContext& ctx) {
  InCalleeScope(ctx, [&](Scope& frame) {
    if (storage.queue) frame.queues[formal] = storage.queue;
    if (storage.assoc) frame.assoc_arrays[formal] = storage.assoc;
  });
  if (storage.holder) ctx.AliasLocalVariable(formal, storage.holder);
}

// §13.5.2 (printed page 348): an argument passed by reference is not copied
// into the subroutine area; the subroutine reaches the original through a
// reference, and the clause's own example passes a fixed-size unpacked array
// so. Lowerer::LowerVar declares a whole variable under every declaration's
// name before LowerVarAggregate gives an aggregate its storage -- element
// variables and an ArrayInfo, a QueueObject or an AssocArrayObject -- so
// TryBindRefArg found that placeholder for `scale(arr)` and aliased the formal
// to a scalar: `a[i]` in the body bit-selected the placeholder, `qq.push_front`
// found no queue and `m["x"]` no associative array, and the caller's aggregate
// stood as it was. Here the formal's name is made to stand in the callee's
// scope for what the actual's name stands for in the caller's: the same
// QueueObject or AssocArrayObject, or the actual's shape with each element
// aliased under the formal's name, and the placeholder beside them, so a
// write through the formal that announces itself by the aggregate's name
// (NotifyOwningVar) reaches the watchers of the caller's declaration.
//
// A multidimensional fixed-size array holds its leaves under `arr[i][j]`
// names this does not alias, so it is left to the bind that follows, as it
// was. §3.12.1 (printed page 56): `push($unit::q)` binds the unit's queue
// by its key (IdentifierLookupKey), as TryBindArrayArg copies it; by the
// text alone a module's own q was bound.
static bool TryBindRefAggregateArg(const Expr* call_arg,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  std::string actual = IdentifierLookupKey(call_arg);
  AggregateStorage storage = FindAggregateStorage(actual, ctx);
  if (!storage.queue && !storage.assoc && !storage.info) return false;
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

  // §13.5.2 forms the reference on "equivalent data types", and §6.18 makes a
  // name standing for the element type equivalent to it. The one-argument
  // EvalTypeWidth gives a DataTypeKind::kNamed no width at all, so a formal
  // written with a typedef answered 0, 0 matched no element width, and the bind
  // was declined -- the argument then fell to the by-value bind and the write
  // reached a copy, which is the opposite of what the clause asks. This is an
  // equivalence gate rather than §10.8's resize, which is why the width is
  // compared rather than applied; what it needed was the width the name stands
  // for.
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
      // §13.5.2 makes this the caller's own element rather than a copy, so the
      // copy-out is a write to the caller's queue and §9.4.2 has it announce
      // itself. Only here, below the `continue` above: an element deleted
      // during the call is written nowhere and so changes nothing. Several
      // bindings can name one aggregate -- `swap(q[0], q[1])` -- and each has
      // changed an element of it, so one notification per binding is the
      // count, a watcher re-evaluating its expression rather than reading a
      // delta.
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
  // §7.8.7: an element passed by reference is allocated when it does not
  // exist, holding the initial value the array gives a new element. The key it
  // is allocated under is the one an assignment to that element would use, so
  // that both statements reach one entry.
  if (aa->is_string_key) {
    binding.str_key = AssocStringKey(EvalExpr(call_arg->index, ctx, arena));
    auto it = aa->str_data.find(binding.str_key);
    if (it == aa->str_data.end()) {
      aa->str_data[binding.str_key] = AssocAllocValue(aa, arena);
      it = aa->str_data.find(binding.str_key);
      // The allocation is itself a change to the caller's array, so it is
      // announced where it happens rather than left for the copy-out, which
      // would make the notification depend on the body having written the
      // formal.
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
    // §13.5.2 and §9.4.2, as for the queue above: the copy-out writes the
    // caller's array, and the watchers are on the variable the array was
    // declared under rather than on the entry.
    NotifyOwningVar(ctx, b.var_name);
  }
}

// §13.5.1: what the actual's evaluation hands the formal -- the value copied
// in and, where the actual is a call whose body returned a tagged union
// expression, the tag §7.3.2 (printed page 151) has travel beside the value's
// bits, which no vector carries; empty for every other actual.
struct ActualValue {
  Logic4Vec value;
  std::string tag;
};

// The actual is the caller's expression and is read with the callee's scope
// set aside; §13.5.3 has a default argument evaluated in the scope of the
// subroutine's declaration, so the default stays with the callee's scope up.
//
// §10.9.2 (printed page 263) evaluates an assignment pattern's members in the
// context of an assignment to the members they initialize, and §11.9 (printed
// 304) has a tagged union expression's type known from its context, here the
// formal, so a pattern actual, bare, typed or under a tagged expression, is
// placed member by member against the formal's layout (TryEvalPatternActual)
// before the general evaluation, which knows no type to place it by, is
// reached. A call's result comes with the tag its body's return gave it
// (EvalWithReturnedTag), for the binding to copy in beside the value.
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
                       ? EvalExpr(param.default_value, ctx, arena)
                       : MakeLogic4Vec(arena, 32);
  return resolved;
}

// §13.5.1: "This argument passing mechanism works by copying each argument into
// the subroutine area ... If the arguments are changed within the subroutine,
// the changes are not visible outside the subroutine", and §13.5.2 draws the
// contrast this and the three binds below erased -- "Arguments passed by
// reference are not copied into the subroutine area". A map assignment
// copy-constructs every entry, and a Logic4Vec copy carries its words pointer
// rather than the words (src/common/types.h), so the formal's entries were the
// actual's: an in-place write to either -- DepositBitField writes through the
// words it finds -- was a write to both. Each entry takes its own words.
static bool TryBindAssocArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  auto* src = ctx.FindAssocArray(IdentifierLookupKey(call_arg));
  if (!src) return false;
  auto* dst =
      ctx.CreateAssocArray(param_name, src->elem_width, src->is_string_key);
  for (const auto& [key, val] : src->int_data)
    dst->int_data[key] = OwnRhsWords(val, arena);
  for (const auto& [key, val] : src->str_data)
    dst->str_data[key] = OwnRhsWords(val, arena);
  dst->has_default = src->has_default;
  dst->default_value = OwnRhsWords(src->default_value, arena);
  dst->index_width = src->index_width;
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  dst->index_class = src->index_class;
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
        Subclause("7.7"));
    return true;
  }
  ArrayInfo finfo;
  finfo.size = static_cast<uint32_t>(formal_size);
  finfo.elem_width = src_q->elem_width;
  finfo.is_4state = src_q->is_4state;
  // §13.4: a formal has the lifetime of the call, so its shape goes away when
  // the call returns, as the per-element formals created just below already do.
  ctx.RegisterArrayInScope(formal.name, finfo);
  for (uint32_t j = 0; j < finfo.size; ++j) {
    auto dst = std::string(formal.name) + "[" + std::to_string(j) + "]";
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), src_q->elements[j].width);
    // §13.5.1, as in TryBindAssocArg above: the element is copied into the
    // subroutine area, words and all.
    dst_var->value = OwnRhsWords(src_q->elements[j], arena);
  }
  return true;
}

// Dynamic arrays and queues hold their elements in a QueueObject rather than
// as per-element variables, so a by-value bind copies through that object. The
// formal becomes a fresh, independent copy of the actual -- which the vector
// assignment alone did not make it: it copy-constructs every Logic4Vec, and
// that carries the words pointer rather than the words, so §13.5.1's copy
// reached the QueueObject and the vector inside it and stopped at every element
// they held.
static bool TryBindQueueArg(QueueObject* src_q, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena, SourceLoc loc) {
  if (formal.unpacked_dims.empty()) return false;
  // §7.10 writes a queue formal's dimension as `[$]` or `[$:N]`, which the
  // parser records as an expression rather than as the null a dynamic array's
  // `[]` leaves. Reading any non-null dimension as §7.4.2's fixed size sent a
  // queue formal to the fixed-size bind, which evaluated the `$` as a size,
  // reported a mismatch and bound nothing -- so the callee's `q[0]` found no
  // formal at all and reached the actual it was called with.
  const Expr* dim = formal.unpacked_dims[0];
  if (dim != nullptr && !IsQueueDim(dim)) {
    return BindQueueToFixedFormal(src_q, formal, ctx, arena, loc);
  }
  // An unsized formal keeps the dynamic-array/queue representation, so the
  // callee reads the copy through the same queue-backed select path.
  auto* dst_q = ctx.CreateQueue(formal.name, src_q->elem_width, src_q->max_size,
                                src_q->is_4state);
  dst_q->elements.reserve(src_q->elements.size());
  for (const auto& elem : src_q->elements)
    dst_q->elements.push_back(OwnRhsWords(elem, arena));
  dst_q->AssignFreshIds();
  return true;
}

// Binds a fixed-size unpacked-array actual by copying each element variable
// into a fresh per-element formal variable.
//
// §13.3 (printed page 337) has an output formal copy its value out at the end
// and nothing in at the beginning, so an output formal's element starts at
// the default a scalar output formal starts at in BindValueArg rather than at
// the caller's element; an input or inout element is the caller's copied in.
//
// §7.4 (printed page 153) puts the packed dimensions before the name and the
// unpacked ones after it, so mytask4's `output [3:0][7:0] y[1:0]` (§13.3,
// printed 337) is two elements of a packed two-dimensional type, and §7.4.1
// makes one index of such an element select a subfield of it, `y[1][3]` the
// eight bits of element 3. The element's variable is created here with no
// record of that layout, so the body's `y[1][3] = 8'hAB` wrote bit 3 of it.
// The formal's declared packed dimensions are recorded as a declaration's are
// (RecordPackedRange), which is what SelectStorageBits reads the index by.
static void BindFixedArrayArg(const Expr* call_arg, const FunctionArg& formal,
                              const ArrayInfo& info, SimContext& ctx,
                              Arena& arena) {
  // §13.4, as above: the shape lives as long as the call does.
  ctx.RegisterArrayInScope(formal.name, info);
  for (uint32_t j = 0; j < info.size; ++j) {
    uint32_t idx = info.lo + j;
    auto src = IdentifierLookupKey(call_arg) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(formal.name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info.elem_width, 0);
    if (formal.direction == Direction::kOutput)
      val = MakeLogic4VecVal(arena, val.width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    // §13.5.1 again: `val` is the caller's element variable's own Logic4Vec
    // where the element exists, so the store takes the words rather than the
    // pointer to them.
    dst_var->value = OwnRhsWords(val, arena);
    RecordPackedRange(&formal.data_type, dst_var, ctx, arena);
  }
}

static bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, formal.name, ctx, arena)) return true;

  if (auto* src_q = ctx.FindQueue(IdentifierLookupKey(call_arg)))
    return TryBindQueueArg(src_q, formal, ctx, arena, call_arg->range.start);

  auto* info = ctx.FindArrayInfo(IdentifierLookupKey(call_arg));
  if (!info) return false;

  BindFixedArrayArg(call_arg, formal, *info, ctx, arena);
  return true;
}

// §13.5.2 (printed page 349) lists an element of an unpacked array among what
// may be passed by reference. A fixed-size array's element is a variable of
// its own, `arr[idx]` (CreateArrayElements in lowerer_var.cpp), so the formal
// is aliased to it as TryBindRefArg aliases a whole variable; the index is the
// caller's expression and is read with the callee's scope set aside, as the
// actuals are. Before this the shape reached neither the queue nor the
// associative-array element bind and fell to the by-value copy, so
// `add(arr[2], 5)` left the element at 40. An element of a multidimensional
// array, `arr[1][2]`, has a select for its base and is not aliased here.
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

// §13.5: the actual argument a formal is bound from -- the call expression and
// the position the actual occupies in its argument list (negative when the call
// supplies none, so the formal takes its default) -- and, once the actual has
// been evaluated, the tag its value carries where it is a call whose body
// returned a tagged union expression (ActualValue::tag), empty otherwise.
struct ActualArgRef {
  const Expr* expr;
  int index;
  std::string_view result_tag;
};

static void RegisterValueArgStructType(const FunctionArg& param,
                                       const ActualArgRef& ref,
                                       SimContext& ctx);

// Attempts the ref-binding strategies (whole aggregate, plain ref, queue
// element, assoc element, fixed-size array element) for a ref-direction
// formal. Returns true when one of them bound the argument. The aggregate bind
// stands first because a declared aggregate's name also finds the whole
// variable the lowerer declares under it, which the plain bind would take for
// the actual.
//
// A structure variable is one variable, so the plain bind aliases it whole;
// what the formal still lacks is the layout, which SimContext keys by the
// variable's name (RegisterStructInfo in lowerer_var.cpp) and so does not
// follow the alias. RegisterValueArgStructType records the actual's layout
// under the formal's name, as it does for a by-value structure formal; without
// it `x.a = 8` through `ref st_t x` resolved to no member of anything.
static bool TryBindRefDirectionArg(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index >= 0 &&
      TryBindRefAggregateArg(expr->args[static_cast<size_t>(arg_index)], param,
                             ctx, arena)) {
    return true;
  }
  if (TryBindRefArg(expr, arg_index, param.name, ctx)) {
    RegisterValueArgStructType(param, {expr, arg_index, {}}, ctx);
    RegisterValueArgClassType(param, ctx);
    // §6.19.5 with §13.5.2: a ref formal declared with an enumeration is an
    // expression of that type inside the body, `c = c.next()`, whatever the
    // actual's own name is recorded under.
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

// §7.3.2 (printed page 151): a tagged union stores its tag beside the member
// value, so the tag is part of what §13.5.1 (printed 348) copies into the
// subroutine's own variable, and §11.9 (printed 304) checks a member access
// of the formal inside the body against it. The formal took the bits alone:
// `a.Valid` of a formal bound from a union holding `tagged Invalid` was read
// against no tag and raised nothing, and %p of the formal printed the
// untagged form. An identifier actual's tag stands under the key its storage
// was created by (TagKeyOfName of DeclaredKindsKey, "$unit.u" for `$unit::u`,
// §3.12.1 printed 56), read with the callee's scope set aside as the layout
// is; a call's is the one its body's return recorded for the actual's
// evaluation, and `f(h())` with h returning `tagged Invalid` raised nothing
// while a call's result reached the formal untagged. Any other actual carries
// none. §13.3 (printed 337) copies nothing into an output formal, so its tag
// starts undefined.
static std::string ActualTag(const FunctionArg& param, const Expr* actual,
                             const ActualArgRef& ref, SimContext& ctx) {
  if (actual == nullptr || param.direction == Direction::kOutput) return {};
  if (actual->kind != ExprKind::kIdentifier) return std::string(ref.result_tag);
  CalleeScopeAside aside(ctx);
  std::string key = TagKeyOfName(DeclaredKindsKey(actual), ctx);
  return std::string(ctx.GetVariableTag(key));
}

// §7.2.2/§13.5.1: make member access (arg.field) work on a by-value struct
// copy. struct_types_ is keyed by variable name, so a named-type formal -- e.g.
// `input s_t arg` -- cannot find its layout by the type name `s_t` (a type name
// is never a registered struct key). Resolve the layout from the actual
// argument's registered struct type and re-register it under the parameter
// name. False when the actual argument is not a resolvable struct identifier.
//
// §23.9 with §13.5: the actual is a name of the caller's, resolved within the
// instance the call runs in, so its layout is asked for by the key that
// instance's storage was created under (DeclaredKindsKey: "$unit.u" for
// `$unit::u`, §3.12.1 printed 56), with the callee's scope set aside as every
// other read of an actual is made. Asked by the bare name, an instance's
// struct bound no layout and a module's own u bound its layout for the unit's.
static bool TryBindIdentifierActualLayout(const FunctionArg& param,
                                          const Expr* actual, SimContext& ctx) {
  if (actual == nullptr || actual->kind != ExprKind::kIdentifier) return false;
  const StructTypeInfo* sinfo = nullptr;
  {
    CalleeScopeAside aside(ctx);
    sinfo = StructLayoutOfName(DeclaredKindsKey(actual), ctx);
  }
  if (sinfo == nullptr) return false;
  // Copy before re-inserting: registering into struct_types_ may rehash and
  // invalidate the reference returned for the source variable.
  StructTypeInfo copy = *sinfo;
  ctx.RegisterStructType(param.name, copy);
  ctx.SetVariableStructType(param.name, param.name);
  return true;
}

// §13.5.1 (printed page 348): the copy the binding makes is a variable of the
// formal's type, so the formal's layout is its declaration's where that
// writes one -- §13.3 (printed 337) takes a structure or union inline there,
// and TryBindInlineAggregateFormal builds it before the actual is looked at;
// resolved from the actual alone, `f(g())` bound no layout and `s.a` in the
// body was read through no member. A typedef-named formal takes an identifier
// actual's layout (TryBindIdentifierActualLayout) and, for any other actual,
// the typedef's own (TryBindNamedAggregateFormal), which a pattern or a call's
// result was bound to none of. §7.3.2 (printed 151) has a union's tag travel
// beside its bits, so a union formal takes the actual's tag (ActualTag) with
// its layout; the tag table is no frame of the call, so the entry is written
// on every bind, empty where nothing is copied in, rather than left holding
// the last call's, which §11.9 (printed 304) would check the body's member
// reads against.
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

// The actual `ref` names in the call, or null where the call passes none
// for the formal.
static const Expr* ActualExprOf(const ActualArgRef& ref) {
  if (ref.index < 0) return nullptr;
  return ref.expr->args[static_cast<size_t>(ref.index)];
}

// §13.3.2: the arguments of a static task/function are static storage that
// retains its value between invocations. On a later call the formal already
// exists in the static-frame store, so reuse that cell instead of a fresh
// default-initialized one: an input/inout formal is refreshed with the value
// just passed, while an output formal keeps whatever it retained from the last
// call (a read-before-write sees the retained value, not the default). An
// automatic task takes the fresh-each-entry path in BindValueArg, per §13.3.2 /
// Claim E. Answers whether the formal was bound to such a cell.
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
    // §6.11.2: the retained cell was marked when the first call created it, so
    // a later call converts into the same answer.
    if (!existing->is_4state) CoerceTo2State(existing->value);
  }
  RegisterValueArgStructType(param, actual, ctx);
  RegisterValueArgClassType(param, ctx);
  return true;
}

// §6.11 (Table 6-8): the integer data types, which §6.12.1's conversion of a
// real takes as its target. A type reached through a name is left alone, as
// what it stands for is not read here.
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

// §10.8 makes passing a value to a subroutine argument an assignment-like
// context, so the actual converts into the formal's declared type as into a
// variable of it. §6.12.1 converts a real assigned to an integer by rounding
// it to the nearest integer, a half away from zero: `fi(12.5)` into `input int
// x` reads 13 and `fb(-3.5)` into a byte -4; the real's 64-bit pattern was
// resized to the formal's width as any vector is, and read 0. The same clause
// converts an integer assigned to a real numerically, so `f(2)` into a `real a`
// reads 2.0 rather than the bits of 2 read as a double, and a real into a
// `shortreal` formal takes the single-precision value at its 32 bits. A formal
// no width can be found for is left as the actual arrived.
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
  // §6.8: a variable is "an abstraction of a data storage element" that
  // "shall store a value from one assignment to the next", and the formal is a
  // second one. EvalExpr answers a bare identifier, an unpacked-array element
  // select and a class property with the source's own Logic4Vec, and a
  // Logic4Vec copies its words pointer, so a formal took the actual's storage.
  // The coercion below is what shows it: §6.11.2 converts "any unknown or
  // high-impedance bits ... to zeros", and it must convert the formal's copy --
  // `note(x)` with a `bit [7:0]` formal cleared the caller's x inside a call
  // that only read it.
  //
  // The copy is taken here, where the value is produced, rather than around the
  // resize below. That resize runs only on a width mismatch and returns its
  // argument untouched when the widths already match, which is precisely the
  // aliased case, so a copy placed within it would leave the defect. Here it
  // also covers the static formal's own store and coercion, which
  // TryReuseStaticFormal reaches before the resize's result gets that far.
  ActualValue resolved = ResolveArgValue(param, expr, arg_index, ctx, arena);
  auto val = OwnRhsWords(resolved.value, arena);
  // The tag the actual's evaluation handed over rides with the actual to the
  // struct binding, whichever of the two paths below reaches it.
  ActualArgRef bound{expr, arg_index, resolved.tag};
  const auto& dt = param.data_type;
  if (dt.kind != DataTypeKind::kImplicit) {
    val = ConvertToFormalType(val, dt, EvalFormalArgWidth(dt, ctx, arena), ctx,
                              arena);
  }
  // 13.3.2/13.5.1: an output formal is not passed a value from the caller; only
  // input and inout formals receive the actual's value. The actual is evaluated
  // above solely to size the formal - reset the bits to the default so a
  // read-before-write (and, for an automatic task, each fresh entry) observes
  // the default value rather than the caller's current value.
  if (param.direction == Direction::kOutput)
    val = MakeLogic4VecVal(arena, val.width, 0);

  bool is_static_sub = func && func->is_static && !func->is_automatic;
  SyncHandle sync = SyncActualOf(param, ActualExprOf(bound), func, ctx, arena);
  if (TryReuseStaticFormal(param, bound, val, func, ctx)) {
    BindSyncFormal(sync, ctx.FindLocalVariable(param.name), ctx);
    return;
  }

  // §6.11.3: a formal is an object declared with a type, so `integer a` is a
  // signed object however the actual arrived. Taking the signedness from the
  // declaration rather than leaving the formal unsigned is what makes `a + b`
  // in the body signed arithmetic; the value copied in below carries the
  // actual's flag, so re-impose the declaration's on the cell too.
  auto* var = ctx.CreateLocalVariable(
      param.name, val.width, DeclaredTypeIsSigned(param.data_type, ctx));
  // §6.11.2: a formal is an object declared with a type, and §10.8 makes "the
  // passing of a value to a subroutine input, output, or inout argument" an
  // assignment-like context, so an unknown copied into a 2-state formal becomes
  // zero. The flag also decides whether an assignment to the formal inside the
  // body converts, which it could not while every formal was left at Variable's
  // 4-state default.
  var->is_4state = DeclaredTypeIs4State(param.data_type);
  // §6.16 with §13.5.1: a formal declared string, `input string s` or
  // `output string o`, is a string the body reads and writes as one, and the
  // mark is what every reader of a string reads (SimContext::IsStringVariable)
  // -- a body local declared string takes it in CreateFuncLocalVar. Left at
  // the default, `s.len()` inside the body found no string under the name and
  // answered 0, and `s.toupper()` "".
  var->is_string = DeclaredTypeIsString(dt, ctx);
  // §6.12 with §13.5.1: a formal declared real, shortreal or realtime is a
  // real variable the body reads and writes as one -- `l = a + b` of two real
  // formals is a real sum, and `x = x + 1.0` into a ref real one a real store.
  // The mark is what the store path reads (ConvertRealOnAssign) and what
  // EvalIdentifier gives the value read; a body local declared so takes it in
  // CreateFuncLocalVar. Left at the default, a formal was real only by the
  // value it arrived with, and a real store into a local of the body converted
  // the sum as into an integer.
  var->is_real = DeclaredTypeIsReal(dt, ctx);
  // §6.19.5 with §13.5.1: a formal declared with an enumeration is an
  // expression of that type inside the body, `c.next().name()` on an input
  // and `c = c.next()` on an output, as a body local declared with one is
  // (CreateFuncLocalVar); unrecorded, the methods found no enumeration under
  // the formal's name and answered 0 or "".
  if (param.unpacked_dims.empty()) RecordVariableEnumType(param.name, dt, ctx);
  // §25.9 has a virtual interface passed as an argument to a task, function or
  // method; the formal is then a virtual interface of its own, and a member
  // the body reaches through it is a component of the instance it holds.
  var->is_virtual_interface = DeclaresAVirtualInterface(dt, ctx);
  var->value = val;
  var->value.is_signed = var->is_signed;
  if (!var->is_4state) CoerceTo2State(var->value);
  if (is_static_sub) ctx.SaveStaticFuncVar(func->name, param.name, var);
  // A named-type struct formal (input s_t arg) has kind kNamed, not kStruct, so
  // resolve from the actual argument unconditionally; the resolver is a no-op
  // for non-struct actuals.
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
      continue;
    }
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)], param,
                                   ctx, arena)) {
      continue;
    }
    BindValueArg(param, {expr, ai, {}}, func, ctx, arena);
  }
}

}  // namespace delta
