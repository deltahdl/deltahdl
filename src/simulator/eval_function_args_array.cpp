#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/static_aggregate.h"
#include "simulator/variable.h"

namespace delta {

uint32_t ElementIndexAt(const ArrayInfo& info, uint32_t k) {
  return info.is_descending ? info.lo + info.size - 1 - k : info.lo + k;
}

uint32_t ArrayElementCount(const ArrayInfo& info) {
  if (info.dim_sizes.empty()) return info.size;
  uint32_t count = 1;
  for (uint32_t size : info.dim_sizes) count *= size;
  return count;
}

std::string ArrayElementSuffixAt(const ArrayInfo& info, uint32_t k) {
  if (info.dim_sizes.empty()) {
    return "[" + std::to_string(ElementIndexAt(info, k)) + "]";
  }
  std::string suffix;
  for (size_t d = info.dim_sizes.size(); d-- > 0;) {
    uint32_t size = info.dim_sizes[d];
    uint32_t pos = size == 0 ? 0 : k % size;
    if (size != 0) k /= size;
    uint32_t lo = d < info.dim_los.size() ? info.dim_los[d] : 0;
    bool descending = d < info.dim_descending.size() && info.dim_descending[d];
    uint32_t idx = descending ? lo + size - 1 - pos : lo + pos;
    suffix.insert(0, "[" + std::to_string(idx) + "]");
  }
  return suffix;
}

namespace {

// §7.4.2 (printed pages 153-154): one fixed-size unpacked dimension as a
// formal declares it, `[4:1]`, or the C-style `[4]` that §7.4.2 makes
// `[0:3]`: its smaller bound, its size and whether it was written from the
// higher bound down. Empty for an unsized, queue or associative dimension, or
// a bound that does not evaluate to an address.
struct FixedDim {
  uint32_t lo = 0;
  uint32_t size = 0;
  bool descending = false;
};

std::optional<FixedDim> FixedDimOf(const Expr* dim, SimContext& ctx,
                                   Arena& arena) {
  if (dim == nullptr || IsQueueDim(dim) || IsAssocIndexDim(dim, ctx))
    return std::nullopt;
  int64_t left = 0;
  int64_t right = 0;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    left = static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64());
    right = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  } else {
    auto size = static_cast<int64_t>(EvalExpr(dim, ctx, arena).ToUint64());
    if (size <= 0) return std::nullopt;
    right = size - 1;
  }
  if (std::min(left, right) < 0) return std::nullopt;
  return FixedDim{static_cast<uint32_t>(std::min(left, right)),
                  static_cast<uint32_t>(std::abs(left - right) + 1),
                  left > right};
}

}  // namespace

// §7.4.2 with §7.7 (printed pages 153 and 162): the shape a formal of fixed-
// size unpacked dimensions declares, with the element width `elem_width`.
// §7.7 accepts an actual of the same sizes whatever its ranges, so the formal
// has its own bounds rather than the actual's. lo/size/is_descending describe
// the outermost dimension, and a formal of several dimensions also has every
// one in dim_los/dim_sizes/dim_descending, as a declared multidimensional
// array does (TryCreateMultiDimArray in lowerer_var.cpp). Empty where any
// dimension is not fixed.
static std::optional<ArrayInfo> FixedFormalShape(const FunctionArg& formal,
                                                 uint32_t elem_width,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  if (formal.unpacked_dims.empty()) return std::nullopt;
  ArrayInfo info;
  info.elem_width = elem_width;
  bool multi = formal.unpacked_dims.size() > 1;
  for (const Expr* dim : formal.unpacked_dims) {
    auto fixed = FixedDimOf(dim, ctx, arena);
    if (!fixed) return std::nullopt;
    if (info.size == 0) {
      info.lo = fixed->lo;
      info.size = fixed->size;
      info.is_descending = fixed->descending;
    }
    if (!multi) continue;
    info.dim_los.push_back(fixed->lo);
    info.dim_sizes.push_back(fixed->size);
    info.dim_descending.push_back(fixed->descending);
  }
  return info;
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
//
// §13.3 (printed page 337) copies nothing into an output formal, so one
// starts with no entries, whatever the actual held; WritebackOutputArgs
// carries its entries back.
static void BindAssocArg(const AssocArrayObject* src, const FunctionArg& formal,
                         SimContext& ctx, Arena& arena) {
  auto* dst =
      ctx.CreateAssocArray(formal.name, src->elem_width, src->is_string_key);
  if (formal.direction != Direction::kOutput) {
    for (const auto& [key, val] : src->int_data)
      dst->int_data[key] = OwnRhsWords(val, arena);
    for (const auto& [key, val] : src->str_data)
      dst->str_data[key] = OwnRhsWords(val, arena);
  }
  dst->has_default = src->has_default;
  dst->default_value = OwnRhsWords(src->default_value, arena);
  dst->index_width = src->index_width;
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  dst->index_class = src->index_class;
  dst->index_type_name = src->index_type_name;
}

namespace {

// §7.7 (printed page 162): the level at which a dynamic array of dynamic
// arrays fails the run-time size check against a formal of several fixed
// dimensions, counted from 1 at the outermost, with the size the formal
// declares there and the size the actual brought.
struct LevelSizeMismatch {
  size_t dim = 0;
  size_t want = 0;
  size_t got = 0;
};

// §7.7 with §7.6 (printed pages 162 and 160): appends to `out`, in row-major
// order, the elements of `q`, a dynamic array or queue at level `d` of the
// actual whose elements below it are dynamic arrays or queues of their own
// (QueueObject::element_queues). Each level shall hold as many elements as the
// formal's dimension there, `sizes[d]`; false at the first that does not,
// with `mismatch` saying where. An element whose queue was never made holds
// none.
bool FlattenElementQueues(const QueueObject& q,
                          const std::vector<uint32_t>& sizes, size_t d,
                          std::vector<Logic4Vec>& out,
                          LevelSizeMismatch& mismatch) {
  if (q.elements.size() != sizes[d]) {
    mismatch = {d + 1, sizes[d], q.elements.size()};
    return false;
  }
  if (d + 1 == sizes.size()) {
    out.insert(out.end(), q.elements.begin(), q.elements.end());
    return true;
  }
  for (uint64_t pos = 0; pos < q.elements.size(); ++pos) {
    auto it = q.element_queues.find(q.ElementQueueKeyAt(pos));
    if (it == q.element_queues.end() || it->second == nullptr) {
      mismatch = {d + 2, sizes[d + 1], 0};
      return false;
    }
    if (!FlattenElementQueues(*it->second, sizes, d + 1, out, mismatch)) {
      return false;
    }
  }
  return true;
}

}  // namespace

// §7.7 (printed page 162): a dynamic array of dynamic arrays, `int d[][]`,
// bound to a formal of several fixed dimensions, `int a[3:1][3:1]`. Each
// level's size is known only now and is checked against the formal's, and
// §7.6 pairs the elements by position, so the element at row-major position k
// of the actual is the formal's leaf at position k under the formal's own
// bounds (ArrayElementSuffixAt). The actual's inner arrays sit in the element
// queues of the outer one, which the one-dimensional bind below never looked
// in, so every leaf of the formal read the default. An output formal takes
// nothing in (§13.3, printed 337) and starts at the default.
static bool BindQueueToMultiDimFormal(const QueueObject& src_q,
                                      const FunctionArg& formal,
                                      ArrayInfo shape, SimContext& ctx,
                                      Arena& arena, SourceLoc loc) {
  bool is_output = formal.direction == Direction::kOutput;
  std::vector<Logic4Vec> leaves;
  LevelSizeMismatch mismatch;
  if (!is_output &&
      !FlattenElementQueues(src_q, shape.dim_sizes, 0, leaves, mismatch)) {
    ctx.GetDiag().Error(
        loc,
        "array size mismatch: formal expects " + std::to_string(mismatch.want) +
            " elements in dimension " + std::to_string(mismatch.dim) +
            ", actual has " + std::to_string(mismatch.got),
        Subclause("7.7"));
    return true;
  }
  shape.is_4state = src_q.is_4state;
  // §13.4: the shape lives as long as the call does.
  ctx.RegisterArrayInScope(formal.name, shape);
  uint32_t count = ArrayElementCount(shape);
  for (uint32_t k = 0; k < count; ++k) {
    auto dst = std::string(formal.name) + ArrayElementSuffixAt(shape, k);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), src_q.elem_width);
    dst_var->value = is_output ? MakeLogic4VecVal(arena, src_q.elem_width, 0)
                               : OwnRhsWords(leaves[k], arena);
  }
  return true;
}

// Binds a dynamic-array/queue actual to a fixed-size formal. §7.7 (printed
// page 162) accepts one of equal size, which "requires run-time check", and
// the elements correspond left to right as §7.6's assignment has them: the
// formal `string arr[4:1]` takes the queue's element 0 at arr[4]. The formal
// is materialized as per-element variables under its own bounds. `loc` is
// where the actual was written, which the size-mismatch report names; the
// formal carries no position of its own. Its size was read by evaluating the
// dimension as an expression, which answers 0 for a range, so `[4:1]` was
// refused every actual of 4.
//
// §13.3 (printed page 337) copies nothing into an output formal, so its size
// is the formal's own and its elements start at the default, as an output
// fixed-size formal bound to a fixed-size actual does in BindFixedArrayArg;
// WritebackOutputArgs gives the actual the formal's elements on return.
static bool BindQueueToFixedFormal(QueueObject* src_q,
                                   const FunctionArg& formal, SimContext& ctx,
                                   Arena& arena, SourceLoc loc) {
  auto shape = FixedFormalShape(formal, src_q->elem_width, ctx, arena);
  if (!shape) return false;
  if (!shape->dim_sizes.empty()) {
    return BindQueueToMultiDimFormal(*src_q, formal, *shape, ctx, arena, loc);
  }
  bool is_output = formal.direction == Direction::kOutput;
  if (!is_output && src_q->elements.size() != shape->size) {
    ctx.GetDiag().Error(
        loc,
        "array size mismatch: formal expects " + std::to_string(shape->size) +
            " elements, actual has " + std::to_string(src_q->elements.size()),
        Subclause("7.7"));
    return true;
  }
  shape->is_4state = src_q->is_4state;
  // §13.4: a formal has the lifetime of the call, so its shape goes away when
  // the call returns, as the per-element formals created just below already do.
  ctx.RegisterArrayInScope(formal.name, *shape);
  for (uint32_t k = 0; k < shape->size; ++k) {
    auto dst = std::string(formal.name) + "[" +
               std::to_string(ElementIndexAt(*shape, k)) + "]";
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), src_q->elem_width);
    // §13.5.1, as in BindAssocArg above: the element is copied into the
    // subroutine area, words and all.
    dst_var->value = is_output ? MakeLogic4VecVal(arena, src_q->elem_width, 0)
                               : OwnRhsWords(src_q->elements[k], arena);
  }
  return true;
}

// Dynamic arrays and queues hold their elements in a QueueObject rather than
// as per-element variables, so a by-value bind copies through that object. The
// formal becomes a fresh, independent copy of the actual -- which the vector
// assignment alone did not make it: it copy-constructs every Logic4Vec, and
// that carries the words pointer rather than the words, so §13.5.1's copy
// reached the QueueObject and the vector inside it and stopped at every element
// they held. An output formal starts empty (§13.3, printed page 337) and is
// carried back by WritebackOutputArgs.
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
  // §7.2 with §7.5: a formal of structure elements, `input T a[]`, is laid
  // out by its element type, so `a[1].f1` in the body reads a member.
  BindNamedLayout(formal.name, formal.data_type, ctx);
  if (formal.direction != Direction::kOutput) {
    dst_q->elements.reserve(src_q->elements.size());
    for (const auto& elem : src_q->elements)
      dst_q->elements.push_back(OwnRhsWords(elem, arena));
  }
  dst_q->AssignFreshIds();
  return true;
}

// Binds a fixed-size unpacked-array actual by copying each element variable
// into a fresh per-element formal variable.
//
// §7.7 (printed page 162) accepts a fixed-size actual of the formal's size
// whatever its range -- `string b[5:2]` for `string arr[4:1]` -- and §7.6
// pairs the elements left to right, so the formal keeps the bounds it
// declares and takes the actual's leftmost element at its own leftmost
// index. The formal stood under the actual's bounds, so `arr[2]` read the
// actual's `b[2]`, the fourth element from the left rather than the third.
// A formal whose shape is not the actual's sizes keeps the actual's bounds.
//
// §7.7's own `fun(int a[3:1][3:1])` takes a two-dimensional actual, whose
// elements are the leaves `b[i][j]` (CreateMultiDimLeaves in lowerer_var.cpp),
// and §7.6 pairs them by position in every dimension. Only `b[k]`, one index
// deep, was copied, which names no leaf, so every element of the formal read
// the default. Every leaf is now copied, named at its position on each side
// (ArrayElementSuffixAt).
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
  ArrayInfo shape = info;
  auto own = FixedFormalShape(formal, info.elem_width, ctx, arena);
  if (own && own->size == info.size && own->dim_sizes == info.dim_sizes) {
    shape.lo = own->lo;
    shape.is_descending = own->is_descending;
    shape.dim_los = own->dim_los;
    shape.dim_descending = own->dim_descending;
  }
  // §13.4, as above: the shape lives as long as the call does.
  ctx.RegisterArrayInScope(formal.name, shape);
  uint32_t count = ArrayElementCount(info);
  for (uint32_t k = 0; k < count; ++k) {
    auto src = IdentifierLookupKey(call_arg) + ArrayElementSuffixAt(info, k);
    auto dst = std::string(formal.name) + ArrayElementSuffixAt(shape, k);
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

// §7.4.2 with §7.5: the shape of the fixed or dynamic array property `ref`
// addresses, a dynamic one counting from 0 up.
ArrayInfo ClassArrayShape(const ClassArrayRef& ref) {
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(ref.lo);
  info.size = ref.size;
  info.elem_width = ref.prop->width;
  info.is_descending = !ref.prop->is_dynamic && ref.prop->array_descending;
  info.is_4state = ref.prop->is_4state;
  return info;
}

// §7.7 (printed page 162) with §8.5 (printed 183): an array property reached
// through a handle, `cnt(h.m)` or `sumf(h.f)`, or by its bare name in a
// method, is an array like any other and
// is copied into an array formal. The property is no variable of the
// caller's, so the identifier binds below found nothing under `h.m`, the
// formal took BindValueArg's scalar, and `a.num()` in the body answered 0.
// The object's associative array or queue is read with the callee's scope set
// aside, as every actual is. A fixed or dynamic array property holds its
// elements on the object one by one (ClassArrayElementKey), so they are read
// from the left into a queue of the call's own, which binds as a dynamic
// array actual does: to a fixed-size formal of its size, or copied whole.
static bool TryBindPropertyArrayArg(const Expr* call_arg,
                                    const FunctionArg& formal, SimContext& ctx,
                                    Arena& arena) {
  AssocArrayObject* assoc = nullptr;
  QueueObject* queue = nullptr;
  QueueObject elements;
  bool is_class_array = false;
  {
    CalleeScopeAside aside(ctx);
    assoc = FindAssocArrayOfBase(call_arg, ctx, arena);
    if (assoc == nullptr) queue = FindQueueOfBase(call_arg, ctx, arena);
    ClassArrayRef ref;
    if (assoc == nullptr && queue == nullptr &&
        ResolveClassArray(call_arg, ctx, arena, ref)) {
      ArrayInfo shape = ClassArrayShape(ref);
      elements.elem_width = shape.elem_width;
      elements.is_4state = shape.is_4state;
      for (uint32_t k = 0; k < shape.size; ++k) {
        elements.elements.push_back(OwnRhsWords(
            ReadClassArrayElement(ref, ElementIndexAt(shape, k), ctx, arena),
            arena));
      }
      is_class_array = true;
    }
  }
  if (assoc != nullptr) {
    BindAssocArg(assoc, formal, ctx, arena);
    return true;
  }
  if (is_class_array) queue = &elements;
  if (queue == nullptr) return false;
  return TryBindQueueArg(queue, formal, ctx, arena, call_arg->range.start);
}

bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                     SimContext& ctx, Arena& arena) {
  if (!call_arg) return false;
  if (call_arg->kind == ExprKind::kMemberAccess &&
      !formal.unpacked_dims.empty()) {
    return TryBindPropertyArrayArg(call_arg, formal, ctx, arena);
  }
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  if (auto* src = ctx.FindAssocArray(IdentifierLookupKey(call_arg))) {
    BindAssocArg(src, formal, ctx, arena);
    return true;
  }

  if (auto* src_q = ctx.FindQueue(IdentifierLookupKey(call_arg)))
    return TryBindQueueArg(src_q, formal, ctx, arena, call_arg->range.start);

  auto* info = ctx.FindArrayInfo(IdentifierLookupKey(call_arg));
  if (info != nullptr) {
    BindFixedArrayArg(call_arg, formal, *info, ctx, arena);
    return true;
  }
  // §8.11: a bare name no declaration answers to is, in a method, the
  // property of the running object, `sum(f)` passing the object's array.
  return !formal.unpacked_dims.empty() &&
         TryBindPropertyArrayArg(call_arg, formal, ctx, arena);
}

// The names of the element variables of the one-dimensional shape `info`
// stands for under `name`, interned: the tables they key keep the view.
static std::vector<std::string_view> ElementNames(std::string_view name,
                                                  const ArrayInfo& info,
                                                  Arena& arena) {
  std::vector<std::string_view> names;
  names.reserve(info.size);
  for (uint32_t k = 0; k < info.size; ++k) {
    names.emplace_back(*arena.Create<std::string>(
        std::string(name) + "[" + std::to_string(info.lo + k) + "]"));
  }
  return names;
}

// An output array formal's elements, each aliased to the variable its
// subroutine kept for it on an earlier call.
static void RestoreStaticElements(std::string_view frame, std::string_view name,
                                  SimContext& ctx, Arena& arena) {
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr) return;
  for (std::string_view elem : ElementNames(name, *info, arena)) {
    if (Variable* kept = ctx.FindStaticFuncVar(frame, elem))
      ctx.AliasLocalVariable(elem, kept);
  }
}

// An array formal's elements, each kept as its subroutine's static variable.
static void RetainStaticElements(std::string_view frame, std::string_view name,
                                 SimContext& ctx, Arena& arena) {
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr) return;
  for (std::string_view elem : ElementNames(name, *info, arena)) {
    if (Variable* var = ctx.FindLocalVariable(elem))
      ctx.SaveStaticFuncVar(frame, elem, var);
  }
}

void KeepStaticArrayFormal(const ModuleItem* func, const FunctionArg& formal,
                           SimContext& ctx, Arena& arena) {
  if (func == nullptr || !func->is_static || func->is_automatic) return;
  if (formal.direction == Direction::kOutput &&
      RestoreStaticAggregate(func->name, formal.name, ctx)) {
    RestoreStaticElements(func->name, formal.name, ctx, arena);
    return;
  }
  RetainStaticAggregate(func->name, formal.name, ctx, arena);
  RetainStaticElements(func->name, formal.name, ctx, arena);
}

}  // namespace delta
