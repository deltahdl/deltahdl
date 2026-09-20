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
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/virtual_interface.h"

namespace delta {

// §13.5: an actual argument is an expression of the caller, read before the
// subroutine's formals exist. BindFunctionArgs runs after the callee's scope
// is pushed, and for a static subroutine §13.3.2 has that scope carry the
// formals of the last call, so an actual named after a formal read the formal:
// error_type(opcode) with `input int opcode` refreshed the formal from itself
// and never saw the caller's opcode change, and an actual named after a formal
// bound just before it read that formal instead of the caller's variable.
// While one of these lives the callee's scope is set aside and the caller's
// stands on top; it is put back when the object goes, so the binding that
// follows the read still lands in the callee's scope.
class CalleeScopeAside {
 public:
  explicit CalleeScopeAside(SimContext& ctx) : ctx_(ctx) {
    std::vector<Scope> stack = ctx_.SwapScopeStack({});
    if (!stack.empty()) {
      callee_ = std::move(stack.back());
      stack.pop_back();
      set_aside_ = true;
    }
    ctx_.SwapScopeStack(std::move(stack));
  }
  ~CalleeScopeAside() {
    if (!set_aside_) return;
    std::vector<Scope> stack = ctx_.SwapScopeStack({});
    stack.push_back(std::move(callee_));
    ctx_.SwapScopeStack(std::move(stack));
  }
  CalleeScopeAside(const CalleeScopeAside&) = delete;
  CalleeScopeAside& operator=(const CalleeScopeAside&) = delete;

 private:
  SimContext& ctx_;
  Scope callee_;
  bool set_aside_ = false;
};

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

static bool TryBindRefArg(const Expr* expr, int arg_index,
                          std::string_view param_name, SimContext& ctx) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  Variable* target = nullptr;
  {
    CalleeScopeAside aside(ctx);
    target = ctx.FindVariable(call_arg->text);
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
// was.
static bool TryBindRefAggregateArg(const Expr* call_arg,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  AggregateStorage storage = FindAggregateStorage(call_arg->text, ctx);
  if (!storage.queue && !storage.assoc && !storage.info) return false;
  if (storage.info && !storage.info->dim_sizes.empty()) return false;
  AliasAggregateObjects(storage, param.name, ctx);
  if (storage.info) {
    ctx.RegisterArrayInScope(param.name, *storage.info);
    if (!storage.queue) {
      AliasFixedArrayElements(call_arg->text, param.name, *storage.info, ctx,
                              arena);
    }
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

// The actual is the caller's expression and is read with the callee's scope
// set aside; §13.5.3 has a default argument evaluated in the scope of the
// subroutine's declaration, so the default stays with the callee's scope up.
static Logic4Vec ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                 int arg_index, SimContext& ctx, Arena& arena) {
  if (arg_index >= 0 && expr->args[static_cast<size_t>(arg_index)] != nullptr) {
    CalleeScopeAside aside(ctx);
    return EvalExpr(expr->args[static_cast<size_t>(arg_index)], ctx, arena);
  }
  if (param.default_value) return EvalExpr(param.default_value, ctx, arena);
  return MakeLogic4Vec(arena, 32);
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
  auto* src = ctx.FindAssocArray(call_arg->text);
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
static void BindFixedArrayArg(const Expr* call_arg, const FunctionArg& formal,
                              const ArrayInfo& info, SimContext& ctx,
                              Arena& arena) {
  // §13.4, as above: the shape lives as long as the call does.
  ctx.RegisterArrayInScope(formal.name, info);
  for (uint32_t j = 0; j < info.size; ++j) {
    uint32_t idx = info.lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(formal.name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info.elem_width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    // §13.5.1 again: `val` is the caller's element variable's own Logic4Vec
    // where the element exists, so the store takes the words rather than the
    // pointer to them.
    dst_var->value = OwnRhsWords(val, arena);
  }
}

static bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, formal.name, ctx, arena)) return true;

  if (auto* src_q = ctx.FindQueue(call_arg->text)) {
    return TryBindQueueArg(src_q, formal, ctx, arena, call_arg->range.start);
  }

  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;

  BindFixedArrayArg(call_arg, formal, *info, ctx, arena);
  return true;
}

static void RegisterValueArgStructType(const FunctionArg& param,
                                       const Expr* expr, int arg_index,
                                       SimContext& ctx);

// Attempts the ref-binding strategies (whole aggregate, plain ref, queue
// element, assoc element) for a ref-direction formal. Returns true when one of
// them bound the argument. The aggregate bind stands first because a declared
// aggregate's name also finds the whole variable the lowerer declares under
// it, which the plain bind would take for the actual.
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
    RegisterValueArgStructType(param, expr, arg_index, ctx);
    RegisterValueArgClassType(param, ctx);
    return true;
  }
  if (TryBindQueueElementRef(expr, arg_index, param, ctx, arena)) return true;
  if (TryBindAssocElementRef(expr, arg_index, param, ctx, arena)) return true;
  return false;
}

// Performs the default by-value bind: resolves the argument value, widens it to
// the formal's declared width when applicable, and creates the local variable.
// Computes a value parameter's declared width using the live simulation scope,
// so a width that references in-scope (class/specialization) parameters -- e.g.
// `logic [W-1:0]` -- resolves to the bound parameter value instead of
// collapsing to 1 bit.
//
// A type carrying no packed dimension of its own is sized by DeclaredTypeWidth
// rather than the one-argument EvalTypeWidth, so that §6.18's user-defined type
// name contributes the width of the type it stands for. EvalTypeWidth gives a
// DataTypeKind::kNamed no width at all, and BindValueArg resizes only a
// non-zero width, so a formal written `nib p` was never resized and held
// whatever width the caller's expression happened to have: `8'hFF` passed to a
// four-bit formal read 255. §10.8 makes "the passing of a value to a subroutine
// input, output, or inout argument" an assignment-like context, so §10.7
// truncates or extends into the formal's declared width.
//
// A class-typed formal is excluded, and answers no width at all rather than
// 64. §8.3 makes a class variable a handle to an object, not an object of a
// width, so there is nothing here for §10.7 to truncate; and the table would
// answer for the name whether or not the width it answered meant anything.
// §8.27's forward declaration `typedef class C;` is the case that shows why:
// it records the name with no type behind it yet, which is DataTypeKind::
// kImplicit, and §6.10 makes that a scalar -- so the table holds 1 for the
// class, and resizing to it would leave one bit of a handle. Whether a class
// name is in the table at all then turns on whether the design happens to
// forward-declare it, which is no basis for a width. CreateFuncLocalVar asks
// ctx.FindClassType the same question for the same reason.
static uint32_t EvalFormalArgWidth(const DataType& dt, SimContext& ctx,
                                   Arena& arena) {
  if (!dt.packed_dim_left || !dt.packed_dim_right) {
    if (!dt.type_name.empty() && ctx.FindClassType(dt.type_name)) return 0;
    // §25.9: a virtual interface formal, declared by the type or by a typedef
    // name standing for it, holds the handle of the instance it represents,
    // as wide as Lowerer::LowerVar makes a variable declared so, which is
    // what an output formal is sized to before the body assigns it.
    if (DeclaresAVirtualInterface(dt, ctx)) return 64;
    return DeclaredTypeWidth(dt, ctx);
  }
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

// §13.5: the actual argument a formal is bound from -- the call expression and
// the position the actual occupies in its argument list (negative when the call
// supplies none, so the formal takes its default).
struct ActualArgRef {
  const Expr* expr;
  int index;
};

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
  RegisterValueArgStructType(param, actual.expr, actual.index, ctx);
  RegisterValueArgClassType(param, ctx);
  return true;
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
  auto val =
      OwnRhsWords(ResolveArgValue(param, expr, arg_index, ctx, arena), arena);
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

  bool is_static_sub = func && func->is_static && !func->is_automatic;
  if (TryReuseStaticFormal(param, actual, val, func, ctx)) return;

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

// §13.5.2: an output or inout formal is copied to its actual when the
// subroutine returns. The actual is an expression of the caller's, so it is
// assigned with the callee's scope, the top of the stack at this point,
// taken off the stack and put back after: an actual spelled like the formal
// would otherwise resolve to the formal and the caller's variable never
// change.
void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena) {
  std::vector<std::pair<const Expr*, Logic4Vec>> writes;
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
    writes.emplace_back(wb_target, local->value);
  }
  if (writes.empty()) return;
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  Scope callee = std::move(stack.back());
  stack.pop_back();
  ctx.SwapScopeStack(std::move(stack));
  for (const auto& [target, value] : writes) {
    PerformBlockingAssign(target, value, ctx, arena);
  }
  stack = ctx.SwapScopeStack({});
  stack.push_back(std::move(callee));
  ctx.SwapScopeStack(std::move(stack));
}
}  // namespace delta
