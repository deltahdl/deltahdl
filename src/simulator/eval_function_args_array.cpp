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
#include "elaborator/type_eval.h"
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
#include "simulator/statement_assign.h"
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
  dst->is_signed = DeclaredTypeIsSigned(formal.data_type, ctx);
  dst->index_class = src->index_class;
  dst->index_type_name = src->index_type_name;
}

namespace {

struct LevelSizeMismatch {
  size_t dim = 0;
  size_t want = 0;
  size_t got = 0;
};

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

struct QueueFormalBinding {
  const QueueObject& src_q;
  const FunctionArg& formal;
  SourceLoc loc;
};

}  // namespace

static bool BindQueueToMultiDimFormal(const QueueFormalBinding& binding,
                                      ArrayInfo shape, SimContext& ctx,
                                      Arena& arena) {
  const QueueObject& src_q = binding.src_q;
  const FunctionArg& formal = binding.formal;
  bool is_output = formal.direction == Direction::kOutput;
  std::vector<Logic4Vec> leaves;
  LevelSizeMismatch mismatch;
  if (!is_output &&
      !FlattenElementQueues(src_q, shape.dim_sizes, 0, leaves, mismatch)) {
    ctx.GetDiag().Error(
        binding.loc,
        "array size mismatch: formal expects " + std::to_string(mismatch.want) +
            " elements in dimension " + std::to_string(mismatch.dim) +
            ", actual has " + std::to_string(mismatch.got),
        Subclause("7.7"));
    return true;
  }
  shape.is_4state = src_q.is_4state;
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

static bool BindQueueToFixedFormal(QueueObject* src_q,
                                   const FunctionArg& formal, SimContext& ctx,
                                   Arena& arena, SourceLoc loc) {
  auto shape = FixedFormalShape(formal, src_q->elem_width, ctx, arena);
  if (!shape) return false;
  if (!shape->dim_sizes.empty()) {
    return BindQueueToMultiDimFormal({*src_q, formal, loc}, *shape, ctx, arena);
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
  ctx.RegisterArrayInScope(formal.name, *shape);
  for (uint32_t k = 0; k < shape->size; ++k) {
    auto dst = std::string(formal.name) + "[" +
               std::to_string(ElementIndexAt(*shape, k)) + "]";
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), src_q->elem_width);
    dst_var->value = is_output ? MakeLogic4VecVal(arena, src_q->elem_width, 0)
                               : OwnRhsWords(src_q->elements[k], arena);
  }
  return true;
}

static bool TryBindQueueArg(QueueObject* src_q, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena, SourceLoc loc) {
  if (formal.unpacked_dims.empty()) return false;
  const Expr* dim = formal.unpacked_dims[0];
  if (dim != nullptr && !IsQueueDim(dim)) {
    return BindQueueToFixedFormal(src_q, formal, ctx, arena, loc);
  }
  auto* dst_q = ctx.CreateQueue(formal.name, src_q->elem_width, src_q->max_size,
                                src_q->is_4state);
  dst_q->is_signed = DeclaredTypeIsSigned(formal.data_type, ctx);
  BindNamedLayout(formal.name, formal.data_type, ctx);
  if (formal.direction != Direction::kOutput) {
    dst_q->elements.reserve(src_q->elements.size());
    for (const auto& elem : src_q->elements)
      dst_q->elements.push_back(OwnRhsWords(elem, arena));
  }
  dst_q->AssignFreshIds();
  return true;
}

bool RefPropertyTarget(const Expr* actual, SimContext& ctx, Arena& arena,
                       ClassObject*& obj, std::string& key) {
  if (actual == nullptr) return false;
  if (actual->kind == ExprKind::kSelect && actual->index != nullptr &&
      actual->index_end == nullptr && actual->base != nullptr &&
      actual->base->kind == ExprKind::kMemberAccess) {
    ClassArrayRef ref;
    if (!ResolveClassArray(actual->base, ctx, arena, ref) ||
        ref.obj == nullptr || ref.static_owner != nullptr ||
        ClassArrayHoldsSubarrays(ref)) {
      return false;
    }
    Logic4Vec idx = EvalExpr(actual->index, ctx, arena);
    if (HasUnknownBits(idx)) return false;
    obj = ref.obj;
    key = ClassArrayRefElementKey(ref, static_cast<int64_t>(idx.ToUint64()));
    return obj->FindPropertyValue(key) != nullptr;
  }
  if (actual->kind != ExprKind::kMemberAccess || actual->is_scope_resolution ||
      actual->lhs == nullptr || actual->rhs == nullptr ||
      actual->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  obj =
      actual->lhs->kind == ExprKind::kIdentifier && actual->lhs->text == "this"
          ? ctx.CurrentThis()
          : ctx.GetClassObject(EvalExpr(actual->lhs, ctx, arena).ToUint64());
  if (obj == nullptr || obj->type == nullptr ||
      obj->type->StaticPropertyDeclarer(actual->rhs->text) != nullptr) {
    return false;
  }
  key = std::string(actual->rhs->text);
  return obj->FindPropertyValue(key) != nullptr;
}

static bool StartsAtX(const DataType& type, const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return Is4stateType(type.kind);
  std::string key =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  if (const EnumTypeInfo* e = ctx.FindEnumType(key)) return e->is_4state;
  if (const StructTypeInfo* s = ctx.FindStructType(key))
    return s->is_packed && HasFourStateMember(*s);
  return Is4stateType(ctx.FindTypeKind(key));
}

Logic4Vec OutputFormalDefault(const DataType& type, uint32_t width,
                              const SimContext& ctx, Arena& arena) {
  return StartsAtX(type, ctx) ? MakeAllX(arena, width)
                              : MakeLogic4VecVal(arena, width, 0);
}

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
  ctx.RegisterArrayInScope(formal.name, shape);
  BindNamedLayout(formal.name, formal.data_type, ctx);
  uint32_t count = ArrayElementCount(info);
  for (uint32_t k = 0; k < count; ++k) {
    auto src = IdentifierLookupKey(call_arg) + ArrayElementSuffixAt(info, k);
    auto dst = std::string(formal.name) + ArrayElementSuffixAt(shape, k);
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info.elem_width, 0);
    if (formal.direction == Direction::kOutput)
      val = OutputFormalDefault(formal.data_type, val.width, ctx, arena);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    dst_var->value = OwnRhsWords(val, arena);
    RecordPackedRange(&formal.data_type, dst_var, ctx, arena);
  }
}

ArrayInfo ClassArrayShape(const ClassArrayRef& ref) {
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(ref.lo);
  info.size = ref.size;
  info.elem_width = ref.prop->width;
  info.is_descending = !ref.prop->is_dynamic && ref.prop->array_descending;
  info.is_4state = ref.prop->is_4state;
  return info;
}

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

static bool TryBindPatternArrayArg(const Expr* call_arg,
                                   const FunctionArg& formal, SimContext& ctx,
                                   Arena& arena) {
  const Expr* pattern = UnwrapTypedPattern(call_arg);
  if (pattern == nullptr || pattern->kind != ExprKind::kAssignmentPattern ||
      formal.direction != Direction::kInput)
    return false;
  uint32_t elem_width = DeclaredTypeWidth(formal.data_type, ctx);
  auto shape =
      FixedFormalShape(formal, elem_width == 0 ? 32 : elem_width, ctx, arena);
  if (!shape || !shape->dim_sizes.empty()) return false;
  shape->is_4state = DeclaredTypeIs4State(formal.data_type, ctx);
  std::vector<Logic4Vec> values;
  values.reserve(shape->size);
  {
    CalleeScopeAside aside(ctx);
    for (uint32_t k = 0; k < shape->size; ++k) {
      values.push_back(PatternItemAt(
          pattern, ArrayPatternTarget{*shape, nullptr}, k, ctx, arena));
    }
  }
  ctx.RegisterArrayInScope(formal.name, *shape);
  for (uint32_t k = 0; k < shape->size; ++k) {
    auto* var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::string(formal.name) + "[" +
                                   std::to_string(ElementIndexAt(*shape, k)) +
                                   "]"),
        shape->elem_width, DeclaredTypeIsSigned(formal.data_type, ctx));
    var->is_4state = shape->is_4state;
    var->value =
        OwnRhsWords(ResizeToWidth(values[k], shape->elem_width, arena), arena);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->value.is_signed = var->is_signed;
  }
  return true;
}

bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                     SimContext& ctx, Arena& arena) {
  if (!call_arg) return false;
  if (TryBindPatternArrayArg(call_arg, formal, ctx, arena)) return true;
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
  return !formal.unpacked_dims.empty() &&
         TryBindPropertyArrayArg(call_arg, formal, ctx, arena);
}

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

static void RestoreStaticElements(std::string_view frame, std::string_view name,
                                  SimContext& ctx, Arena& arena) {
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr) return;
  for (std::string_view elem : ElementNames(name, *info, arena)) {
    if (Variable* kept = ctx.FindStaticFuncVar(frame, elem))
      ctx.AliasLocalVariable(elem, kept);
  }
}

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
