#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
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

static Logic4Vec ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                 int arg_index, SimContext& ctx, Arena& arena) {
  if (arg_index >= 0 && expr->args[static_cast<size_t>(arg_index)] != nullptr) {
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
  if (formal.unpacked_dims[0] != nullptr) {
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
  auto* var = ctx.CreateLocalVariable(param.name, val.width,
                                      IsSignedType(param.data_type, {}));
  // §6.11.2: a formal is an object declared with a type, and §10.8 makes "the
  // passing of a value to a subroutine input, output, or inout argument" an
  // assignment-like context, so an unknown copied into a 2-state formal becomes
  // zero. The flag also decides whether an assignment to the formal inside the
  // body converts, which it could not while every formal was left at Variable's
  // 4-state default.
  var->is_4state = DeclaredTypeIs4State(param.data_type);
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
