#include "simulator/eval_class_array.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

std::string ClassArrayElementKey(std::string_view name, int64_t index) {
  return std::string(name) + "[" + std::to_string(index) + "]";
}

void DropDroppedElementModes(std::unordered_map<std::string, bool>& modes,
                             std::string_view member, int64_t size) {
  const std::string kPrefix = std::string(member) + "[";
  std::erase_if(modes, [&](const auto& entry) {
    return entry.first.starts_with(kPrefix) &&
           std::strtoll(entry.first.c_str() + kPrefix.size(), nullptr, 10) >=
               size;
  });
}

std::string ClassArraySizeKey(std::string_view name) {
  return std::string(name) + ".size";
}

std::string ClassArrayRefElementKey(const ClassArrayRef& ref, int64_t index) {
  return ClassArrayElementKey(ref.path.empty() ? ref.prop->name : ref.path,
                              index);
}

bool ClassArrayHoldsSubarrays(const ClassArrayRef& ref) {
  return ref.dim + 1 < ref.prop->dim_sizes.size();
}

const ClassTypeInfo::PropertyInfo* FindClassArrayProperty(
    const ClassTypeInfo* type, std::string_view name) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name != name) continue;
      return prop.IsArray() || prop.dim_sizes.size() >= 2 ? &prop : nullptr;
    }
  }
  return nullptr;
}

uint32_t ClassArraySize(const ClassObject* obj,
                        const ClassTypeInfo::PropertyInfo& prop) {
  if (!prop.is_dynamic) return prop.array_size;
  auto it = obj->properties.find(ClassArraySizeKey(prop.name));
  if (it == obj->properties.end()) return 0;
  return static_cast<uint32_t>(it->second.ToUint64());
}

namespace {

const Logic4Vec* FindSlot(const ClassArrayRef& ref, const std::string& key) {
  if (ref.static_owner != nullptr) {
    auto it = ref.static_owner->static_properties.find(key);
    return it != ref.static_owner->static_properties.end() ? &it->second
                                                           : nullptr;
  }
  auto it = ref.obj->properties.find(key);
  return it != ref.obj->properties.end() ? &it->second : nullptr;
}

void SetSlot(const ClassArrayRef& ref, const std::string& key,
             const Logic4Vec& value, SimContext& ctx) {
  if (ref.static_owner != nullptr) {
    ref.static_owner->static_properties[key] = value;
    return;
  }
  ref.obj->SetProperty(key, value);
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
}

ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena) {
  if (side->kind == ExprKind::kIdentifier && side->text == "this")
    return ctx.CurrentThis();
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

bool IndexInRange(const ClassArrayRef& ref, int64_t index) {
  return index >= ref.lo && index < ref.lo + static_cast<int64_t>(ref.size);
}

Logic4Vec ElementDefault(const ClassTypeInfo::PropertyInfo& prop,
                         Arena& arena) {
  return prop.is_4state ? MakeAllX(arena, prop.width)
                        : MakeLogic4VecVal(arena, prop.width, 0);
}

ClassArrayRef MakeRef(ClassObject* obj, const ClassTypeInfo* type,
                      const ClassTypeInfo::PropertyInfo* prop, bool bare) {
  ClassArrayRef ref{obj, prop, bare, prop->array_size,
                    prop->is_dynamic ? 0 : prop->array_lo};
  if (prop->is_static)
    ref.static_owner = type->StaticPropertyDeclarer(prop->name);
  if (ref.static_owner == nullptr && obj == nullptr) {
    ref.static_owner = type;
  }
  if (prop->is_dynamic) {
    const Logic4Vec* count = FindSlot(ref, ClassArraySizeKey(prop->name));
    ref.size = count != nullptr ? static_cast<uint32_t>(count->ToUint64()) : 0;
  }
  if (prop->dim_sizes.size() >= 2) {
    ref.size = prop->dim_sizes[0];
    ref.lo = prop->dim_los[0];
  }
  return ref;
}

const Expr* CallReceiver(const Expr* expr, std::string_view& method) {
  if (expr == nullptr || expr->kind != ExprKind::kCall || expr->lhs == nullptr)
    return nullptr;
  const Expr* access = expr->lhs;
  if (access->kind != ExprKind::kMemberAccess || access->is_scope_resolution ||
      access->lhs == nullptr || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  method = access->rhs->text;
  return access->lhs;
}

bool IsOrderingMethod(std::string_view method) {
  return method == "sort" || method == "rsort" || method == "reverse" ||
         method == "shuffle";
}

int64_t IndexFromLeft(const ClassArrayRef& ref, uint32_t i) {
  return ref.prop->array_descending
             ? ref.lo + static_cast<int64_t>(ref.size) - 1 - i
             : ref.lo + i;
}

Logic4Vec WithValue(const Expr* expr, const Logic4Vec& elem, int64_t index,
                    SimContext& ctx, Arena& arena) {
  if (expr->with_expr == nullptr) return elem;
  IterNames names = ExtractIterNames(expr);
  ctx.PushScope();
  ctx.CreateLocalVariable(names.iter_name, elem.width, elem.is_signed)->value =
      elem;
  ctx.CreateLocalVariable(names.idx_var_name, 32)->value =
      MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(index));
  Logic4Vec value = EvalExpr(expr->with_expr, ctx, arena);
  ctx.PopScope();
  return value;
}

std::vector<Logic4Vec> SortKeys(const Expr* expr, const ClassArrayRef& ref,
                                const std::vector<Logic4Vec>& elems,
                                SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> keys;
  keys.reserve(elems.size());
  for (uint32_t i = 0; i < elems.size(); ++i)
    keys.push_back(
        WithValue(expr, elems[i], IndexFromLeft(ref, i), ctx, arena));
  return keys;
}

std::vector<size_t> SortOrder(const std::vector<Logic4Vec>& keys, bool as_text,
                              bool ascending) {
  auto before = [&](size_t a, size_t b) {
    if (as_text) return Logic4VecToString(keys[a]) < Logic4VecToString(keys[b]);
    return OrdersBefore(keys[a], keys[b], keys[a].is_signed);
  };
  std::vector<size_t> order(keys.size());
  std::iota(order.begin(), order.end(), 0);
  std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return ascending ? before(a, b) : before(b, a);
  });
  return order;
}

bool OrderClassArray(const Expr* expr, const ClassArrayRef& ref,
                     std::string_view method, SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> elems;
  elems.reserve(ref.size);
  for (uint32_t i = 0; i < ref.size; ++i) {
    elems.push_back(
        ReadClassArrayElement(ref, IndexFromLeft(ref, i), ctx, arena));
    elems.back().is_signed = ref.prop->is_signed;
  }
  std::vector<size_t> order(elems.size());
  std::iota(order.begin(), order.end(), 0);
  if (method == "reverse") {
    std::reverse(order.begin(), order.end());
  } else if (method == "shuffle") {
    for (size_t i = order.size(); i > 1; --i)
      std::swap(order[i - 1], order[ctx.Urandom32() % i]);
  } else {
    const bool kText = expr->with_expr == nullptr && ref.prop->is_string;
    order = SortOrder(SortKeys(expr, ref, elems, ctx, arena), kText,
                      method == "sort");
  }
  for (uint32_t i = 0; i < elems.size(); ++i) {
    StoreClassArrayElement(ref, IndexFromLeft(ref, i), elems[order[i]], ctx,
                           arena);
  }
  return true;
}

ClassArrayRef SubarrayAt(const ClassArrayRef& ref, int64_t index) {
  ClassArrayRef sub = ref;
  sub.path = ClassArrayRefElementKey(ref, index);
  sub.dim = ref.dim + 1;
  sub.lo = ref.prop->dim_los[sub.dim];
  sub.size = ref.prop->dim_sizes[sub.dim];
  return sub;
}

struct ClassArrayLeaf {
  ClassArrayRef ref;
  int64_t index;
  std::string name;
};

void CollectLeaves(const ClassArrayRef& ref, const std::string& name,
                   std::vector<ClassArrayLeaf>& out) {
  for (uint32_t i = 0; i < ref.size; ++i) {
    int64_t index = ref.lo + i;
    std::string child = name + "[" + std::to_string(index) + "]";
    if (ClassArrayHoldsSubarrays(ref)) {
      CollectLeaves(SubarrayAt(ref, index), child, out);
    } else {
      out.push_back({ref, index, std::move(child)});
    }
  }
}

bool StoreNestedClassArrayPattern(const ClassArrayRef& dst, const Expr* rhs,
                                  SimContext& ctx, Arena& arena) {
  const ClassTypeInfo::PropertyInfo& prop = *dst.prop;
  const auto kFrom = static_cast<std::ptrdiff_t>(dst.dim);
  ArrayInfo shape;
  shape.dim_los.assign(prop.dim_los.begin() + kFrom, prop.dim_los.end());
  shape.dim_sizes.assign(prop.dim_sizes.begin() + kFrom, prop.dim_sizes.end());
  shape.dim_descending.assign(shape.dim_sizes.size(), false);
  for (size_t d = 0; d < shape.dim_descending.size(); ++d) {
    size_t at = dst.dim + d;
    shape.dim_descending[d] =
        at < prop.dim_descending.size() && prop.dim_descending[at];
  }
  shape.lo = shape.dim_los[0];
  shape.size = shape.dim_sizes[0];
  shape.elem_width = prop.width;
  shape.is_4state = prop.is_4state;
  std::vector<ClassArrayLeaf> leaves;
  CollectLeaves(dst, "$pattern", leaves);
  ctx.PushScope();
  for (const ClassArrayLeaf& leaf : leaves) {
    ctx.CreateLocalVariable(*arena.Create<std::string>(leaf.name), prop.width,
                            prop.is_signed);
  }
  DistributePatternToArray("$pattern", shape, rhs, ctx, arena);
  for (const ClassArrayLeaf& leaf : leaves) {
    StoreClassArrayElement(leaf.ref, leaf.index,
                           ctx.FindVariable(leaf.name)->value, ctx, arena);
  }
  ctx.PopScope();
  return true;
}

}  // namespace

bool NamesOwnArrayProperty(const Expr* base, SimContext& ctx) {
  if (base == nullptr || base->kind != ExprKind::kIdentifier ||
      ctx.FindLocalVariable(base->text) != nullptr)
    return false;
  const ClassObject* self = ctx.CurrentThis();
  return self != nullptr &&
         FindClassArrayProperty(self->type, base->text) != nullptr;
}

static bool ResolveBareClassArray(const Expr* base, SimContext& ctx,
                                  ClassArrayRef& out) {
  if (ctx.FindLocalVariable(base->text) != nullptr) return false;
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* type =
      self != nullptr ? self->type : ctx.CurrentMethodClass();
  if (type == nullptr) return false;
  const auto* prop = FindClassArrayProperty(type, base->text);
  if (prop == nullptr || (self == nullptr && !prop->is_static)) return false;
  out = MakeRef(self, type, prop, true);
  if (auto* size = ctx.FindVariable(ClassArraySizeKey(base->text)))
    out.size = static_cast<uint32_t>(size->value.ToUint64());
  return true;
}

static bool ResolveScopedClassArray(const Expr* base, SimContext& ctx,
                                    Arena& arena, ClassArrayRef& out) {
  if (base->lhs->kind != ExprKind::kIdentifier) return false;
  const ClassTypeInfo* cls = ScopeNamedSpecialization(base->lhs, ctx, arena);
  if (cls == nullptr) cls = ctx.FindClassType(base->lhs->text);
  if (cls == nullptr) return false;
  const auto* prop = FindClassArrayProperty(cls, base->rhs->text);
  if (prop == nullptr || !prop->is_static) return false;
  out = MakeRef(nullptr, cls, prop, false);
  return true;
}

static bool ResolveClassSubarray(const Expr* sel, SimContext& ctx, Arena& arena,
                                 ClassArrayRef& out) {
  if (sel->index == nullptr || sel->index_end != nullptr) return false;
  ClassArrayRef outer;
  if (!ResolveClassArray(sel->base, ctx, arena, outer) ||
      !ClassArrayHoldsSubarrays(outer)) {
    return false;
  }
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  if (HasUnknownBits(idx)) return false;
  out = SubarrayAt(outer, static_cast<int64_t>(idx.ToUint64()));
  return true;
}

bool ResolveClassArray(const Expr* base, SimContext& ctx, Arena& arena,
                       ClassArrayRef& out) {
  if (base == nullptr) return false;
  if (base->kind == ExprKind::kIdentifier)
    return ResolveBareClassArray(base, ctx, out);
  if (base->kind == ExprKind::kSelect)
    return ResolveClassSubarray(base, ctx, arena, out);
  if (base->kind != ExprKind::kMemberAccess || base->lhs == nullptr ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (base->is_scope_resolution)
    return ResolveScopedClassArray(base, ctx, arena, out);
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return false;
  const auto* prop = FindClassArrayProperty(obj->type, base->rhs->text);
  if (prop == nullptr) return false;
  out = MakeRef(obj, obj->type, prop, false);
  return true;
}

void ResizeClassArray(const ClassArrayRef& ref, uint32_t size,
                      const ClassArrayRef* init, SimContext& ctx,
                      Arena& arena) {
  for (uint32_t i = 0; i < size; ++i) {
    Logic4Vec val =
        init != nullptr && i < init->size
            ? OwnRhsWords(ReadClassArrayElement(*init, i, ctx, arena), arena)
            : ElementDefault(*ref.prop, arena);
    SetSlot(ref, ClassArrayRefElementKey(ref, i), val, ctx);
  }
  SetSlot(ref, ClassArraySizeKey(ref.prop->name),
          MakeLogic4VecVal(arena, 32, size), ctx);
}

Logic4Vec ReadClassArrayElement(const ClassArrayRef& ref, int64_t index,
                                SimContext& ctx, Arena& arena) {
  if (!IndexInRange(ref, index)) return ElementDefault(*ref.prop, arena);
  std::string key = ClassArrayRefElementKey(ref, index);
  if (ref.bare) {
    if (auto* local = ctx.FindVariable(key)) return local->value;
  }
  if (ref.static_owner != nullptr) {
    const Logic4Vec* held = FindSlot(ref, key);
    return held != nullptr ? *held : ElementDefault(*ref.prop, arena);
  }
  return ref.obj->GetProperty(key, arena);
}

bool TryClassArrayElementSelect(const Expr* expr, int64_t index,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (expr->index_end != nullptr) return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(expr->base, ctx, arena, ref)) return false;
  out = ReadClassArrayElement(ref, index, ctx, arena);
  return true;
}

bool TryEvalClassArrayMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  std::string_view method;
  const Expr* receiver = CallReceiver(expr, method);
  if (receiver == nullptr) return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(receiver, ctx, arena, ref)) return false;
  if (method == "size") {
    out = MakeLogic4VecVal(arena, 32, ref.size);
    return true;
  }
  if (method == "delete" && ref.prop->is_dynamic) {
    ResizeClassArray(ref, 0, nullptr, ctx, arena);
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return IsOrderingMethod(method) &&
         OrderClassArray(expr, ref, method, ctx, arena);
}

bool TryWriteClassArrayElement(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect ||
      lhs->index_end != nullptr) {
    return false;
  }
  ClassArrayRef ref;
  if (!ResolveClassArray(lhs->base, ctx, arena, ref)) return false;
  Logic4Vec idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return true;
  StoreClassArrayElement(ref, static_cast<int64_t>(idx_val.ToUint64()), rhs_val,
                         ctx, arena);
  return true;
}

bool TryWriteClassArrayElementChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect ||
      lhs->index_end != nullptr || lhs->base == nullptr ||
      lhs->base->kind != ExprKind::kSelect || lhs->base->index_end != nullptr)
    return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(lhs->base->base, ctx, arena, ref) ||
      !ref.prop->is_string || ClassArrayHoldsSubarrays(ref))
    return false;
  Logic4Vec at = EvalExpr(lhs->base->index, ctx, arena);
  Logic4Vec pos = EvalExpr(lhs->index, ctx, arena);
  auto index = static_cast<int64_t>(at.ToUint64());
  if (HasUnknownBits(at) || HasUnknownBits(pos) || !IndexInRange(ref, index))
    return true;
  std::string text =
      Logic4VecToString(ReadClassArrayElement(ref, index, ctx, arena));
  uint64_t i = pos.ToUint64();
  auto byte = static_cast<char>(rhs_val.ToUint64() & 0xFF);
  if (i >= text.size() || byte == 0) return true;
  text[i] = byte;
  StoreClassArrayElement(ref, index, StringToLogic4Vec(arena, text), ctx,
                         arena);
  return true;
}

bool TryWriteClassArrayElementBits(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect ||
      lhs->base == nullptr || lhs->base->kind != ExprKind::kSelect ||
      lhs->base->index_end != nullptr)
    return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(lhs->base->base, ctx, arena, ref) ||
      ref.prop->is_string || ref.prop->is_real || ClassArrayHoldsSubarrays(ref))
    return false;
  Logic4Vec at = EvalExpr(lhs->base->index, ctx, arena);
  auto index = static_cast<int64_t>(at.ToUint64());
  if (HasUnknownBits(at) || !IndexInRange(ref, index)) return true;
  Variable element;
  element.value =
      OwnRhsWords(ReadClassArrayElement(ref, index, ctx, arena), arena);
  element.is_4state = ref.prop->is_4state;
  element.is_signed = ref.prop->is_signed;
  const ClassTypeInfo* type =
      ref.static_owner != nullptr ? ref.static_owner : ref.obj->type;
  if (auto range = PropertyDeclaredRange(type, ref.prop->name,
                                         element.value.width, ctx, arena)) {
    element.packed_range = *range;
    element.has_packed_range = true;
  }
  WriteBitSelect(&element, lhs, rhs_val, ctx, arena);
  StoreClassArrayElement(ref, index, element.value, ctx, arena);
  return true;
}

void StoreClassArrayElement(const ClassArrayRef& ref, int64_t index,
                            const Logic4Vec& value, SimContext& ctx,
                            Arena& arena) {
  if (!IndexInRange(ref, index)) return;
  Logic4Vec stored = CoerceToPropertyType(
      ref.static_owner != nullptr ? ref.static_owner : ref.obj->type,
      ref.prop->name, value, arena);
  SetSlot(ref, ClassArrayRefElementKey(ref, index), stored, ctx);
}

bool TryClassArrayNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const Expr* rhs = stmt->rhs;
  if (rhs == nullptr || rhs->kind != ExprKind::kCall || rhs->text != "new" ||
      rhs->args.empty()) {
    return false;
  }
  ClassArrayRef ref;
  if (!ResolveClassArray(stmt->lhs, ctx, arena, ref) || !ref.prop->is_dynamic)
    return false;
  Logic4Vec size_val = EvalExpr(rhs->args[0], ctx, arena);
  int64_t size = LongintValue(size_val);
  if (size < 0) {
    ctx.GetDiag().Error(rhs->args[0]->range.start,
                        "dynamic array new[] size is negative",
                        Subclause("7.5.1"));
    return true;
  }
  ClassArrayRef init;
  bool has_init =
      rhs->args.size() > 1 && ResolveClassArray(rhs->args[1], ctx, arena, init);
  ResizeClassArray(ref, static_cast<uint32_t>(size), has_init ? &init : nullptr,
                   ctx, arena);
  DropDroppedElementModes(ref.static_owner != nullptr
                              ? ref.static_owner->static_rand_active
                              : ref.obj->rand_active,
                          ref.prop->name, size);
  return true;
}

bool PropertyArrayElements(const Expr* src, SimContext& ctx, Arena& arena,
                           std::vector<Logic4Vec>& out) {
  if (src == nullptr || (src->kind != ExprKind::kIdentifier &&
                         src->kind != ExprKind::kMemberAccess)) {
    return false;
  }
  ClassArrayRef ref;
  if (ResolveClassArray(src, ctx, arena, ref)) {
    if (ClassArrayHoldsSubarrays(ref)) return false;
    for (uint32_t i = 0; i < ref.size; ++i)
      out.push_back(
          ReadClassArrayElement(ref, IndexFromLeft(ref, i), ctx, arena));
    return true;
  }
  const QueueObject* q = FindQueueOfBase(src, ctx, arena);
  if (q == nullptr) return false;
  out = q->elements;
  return true;
}

static bool AssignQueueProperty(const Expr* lhs,
                                const std::vector<Logic4Vec>& elems,
                                SimContext& ctx, Arena& arena) {
  if (lhs->kind == ExprKind::kIdentifier &&
      ctx.FindQueue(lhs->text) != nullptr) {
    return false;
  }
  ClassObject* owner = nullptr;
  QueueObject* q = FindQueueOfBase(lhs, ctx, arena, &owner);
  if (q == nullptr) return false;
  q->elements.clear();
  for (const auto& elem : elems)
    q->elements.push_back(
        SizedForQueueElement(*q, OwnRhsWords(elem, arena), arena));
  q->AssignFreshIds();
  ++q->generation;
  AnnounceQueueChange(lhs, owner, ctx);
  return true;
}

static bool PatternItemCount(const Expr* rhs, SimContext& ctx, Arena& arena,
                             uint32_t& out) {
  if (!rhs->pattern_keys.empty()) return false;
  out = static_cast<uint32_t>(rhs->elements.size());
  if (out != 1 || !rhs->elements[0]->is_pattern_replication) return true;
  const Expr* rep = rhs->elements[0];
  Logic4Vec count = EvalExpr(rep->repeat_count, ctx, arena);
  if (!count.IsKnown()) return false;
  out = static_cast<uint32_t>(count.ToUint64() * rep->elements.size());
  return true;
}

bool StoreClassArrayPattern(const ClassArrayRef& dst_ref, const Expr* rhs,
                            SimContext& ctx, Arena& arena) {
  if (ClassArrayHoldsSubarrays(dst_ref))
    return StoreNestedClassArrayPattern(dst_ref, rhs, ctx, arena);
  ClassArrayRef dst = dst_ref;
  if (dst.prop->is_dynamic) {
    if (!PatternItemCount(rhs, ctx, arena, dst.size)) return false;
    ResizeClassArray(dst, dst.size, nullptr, ctx, arena);
  }
  ArrayInfo shape;
  shape.lo = static_cast<uint32_t>(dst.lo);
  shape.size = dst.size;
  shape.is_descending = dst.prop->array_descending;
  shape.elem_width = dst.prop->width;
  shape.is_4state = dst.prop->is_4state;
  const ArrayPatternTarget kTarget{shape, nullptr};
  for (uint32_t i = 0; i < dst.size; ++i) {
    StoreClassArrayElement(dst, IndexFromLeft(dst, i),
                           PatternItemAt(rhs, kTarget, i, ctx, arena), ctx,
                           arena);
  }
  return true;
}

bool TryClassArrayWholeAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const Expr* lhs = stmt->lhs;
  const bool kPattern =
      stmt->rhs != nullptr && stmt->rhs->kind == ExprKind::kAssignmentPattern;
  if (lhs == nullptr || (lhs->kind != ExprKind::kIdentifier &&
                         lhs->kind != ExprKind::kMemberAccess &&
                         (!kPattern || lhs->kind != ExprKind::kSelect))) {
    return false;
  }
  if (kPattern) {
    ClassArrayRef pattern_dst;
    return ResolveClassArray(lhs, ctx, arena, pattern_dst) &&
           StoreClassArrayPattern(pattern_dst, stmt->rhs, ctx, arena);
  }
  std::vector<Logic4Vec> elems;
  if (!PropertyArrayElements(stmt->rhs, ctx, arena, elems)) return false;
  ClassArrayRef dst;
  if (!ResolveClassArray(lhs, ctx, arena, dst))
    return AssignQueueProperty(lhs, elems, ctx, arena);
  if (ClassArrayHoldsSubarrays(dst)) return false;
  if (dst.prop->is_dynamic) {
    dst.size = static_cast<uint32_t>(elems.size());
    ResizeClassArray(dst, dst.size, nullptr, ctx, arena);
  }
  for (uint32_t i = 0; i < dst.size && i < elems.size(); ++i)
    StoreClassArrayElement(dst, IndexFromLeft(dst, i), elems[i], ctx, arena);
  return true;
}

}  // namespace delta
