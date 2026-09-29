#include "simulator/eval_class_array.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
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

// §8.9: the value `ref` holds under `key` -- in the declaring class for a
// static property, in the object for any other -- or null where it holds
// none.
const Logic4Vec* FindSlot(const ClassArrayRef& ref, const std::string& key) {
  if (ref.static_owner != nullptr) {
    auto it = ref.static_owner->static_properties.find(key);
    return it != ref.static_owner->static_properties.end() ? &it->second
                                                           : nullptr;
  }
  auto it = ref.obj->properties.find(key);
  return it != ref.obj->properties.end() ? &it->second : nullptr;
}

// Writes `value` under `key` where `ref` holds its elements, and tells the
// object's watchers of the change (§9.4.2); a static property's storage is
// the class's.
void SetSlot(const ClassArrayRef& ref, const std::string& key,
             const Logic4Vec& value, SimContext& ctx) {
  if (ref.static_owner != nullptr) {
    ref.static_owner->static_properties[key] = value;
    return;
  }
  ref.obj->SetProperty(key, value);
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
}

// The object a member access's handle side names: the running method's object
// for `this`, else the object the handle the side evaluates to refers to.
ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena) {
  if (side->kind == ExprKind::kIdentifier && side->text == "this")
    return ctx.CurrentThis();
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

// Whether `index` addresses an element of the array `ref`.
bool IndexInRange(const ClassArrayRef& ref, int64_t index) {
  return index >= ref.lo && index < ref.lo + static_cast<int64_t>(ref.size);
}

// §7.4/§7.5.1: the value an element of `prop` holds before anything is
// written to it, the element type's x or 0.
Logic4Vec ElementDefault(const ClassTypeInfo::PropertyInfo& prop,
                         Arena& arena) {
  return prop.is_4state ? MakeAllX(arena, prop.width)
                        : MakeLogic4VecVal(arena, prop.width, 0);
}

// The reference `obj` and `prop` make, with the elements the object holds,
// or, for a static property, the elements the class `type` or the base
// declaring it holds (§8.9); `obj` may then be null.
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

// The receiver and the method of a call `receiver.method(...)`, or null for a
// call of any other shape.
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

// §7.12.3: the identity of the operand a reduction method named `method`
// joins the elements by, from which a fold over any count of elements is
// defined; false for a name that is no reduction method.
bool ReductionIdentity(std::string_view method, uint64_t& acc) {
  if (method == "sum" || method == "or" || method == "xor") {
    acc = 0;
  } else if (method == "product") {
    acc = 1;
  } else if (method == "and") {
    acc = ~static_cast<uint64_t>(0);
  } else {
    return false;
  }
  return true;
}

// §7.12.3: `acc` joined with the element value `v` by the method's operand.
uint64_t Join(std::string_view method, uint64_t acc, uint64_t v) {
  if (method == "sum") return acc + v;
  if (method == "product") return acc * v;
  if (method == "and") return acc & v;
  if (method == "or") return acc | v;
  return acc ^ v;
}

// §7.12.3: the value the with clause of the call `expr` maps the element
// `elem` at `index` to, the iterator and its index bound as §7.12 names
// them; the element itself where the call has no with clause.
Logic4Vec WithValue(const Expr* expr, const Logic4Vec& elem, uint32_t index,
                    SimContext& ctx, Arena& arena) {
  if (expr->with_expr == nullptr) return elem;
  IterNames names = ExtractIterNames(expr);
  ctx.PushScope();
  ctx.CreateLocalVariable(names.iter_name, elem.width, elem.is_signed)->value =
      elem;
  ctx.CreateLocalVariable(names.idx_var_name, 32)->value =
      MakeLogic4VecVal(arena, 32, index);
  Logic4Vec value = EvalExpr(expr->with_expr, ctx, arena);
  ctx.PopScope();
  return value;
}

// §7.12.3/§18.5.7.2: the elements of `ref` reduced by the method `method`,
// each through the with clause of `expr` where it has one, into a result of
// the element type, or of the with clause's expression, which the fold is
// held to.
Logic4Vec ReduceClassArray(const Expr* expr, const ClassArrayRef& ref,
                           std::string_view method, SimContext& ctx,
                           Arena& arena) {
  uint64_t acc = 0;
  ReductionIdentity(method, acc);
  Logic4Vec result =
      WithValue(expr, ElementDefault(*ref.prop, arena), 0, ctx, arena);
  for (uint32_t i = 0; i < ref.size; ++i) {
    Logic4Vec elem = ReadClassArrayElement(ref, ref.lo + i, ctx, arena);
    acc = Join(method, acc, WithValue(expr, elem, i, ctx, arena).ToUint64());
  }
  Logic4Vec out = MakeLogic4VecVal(arena, result.width, acc);
  out.is_signed = result.is_signed;
  return out;
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

// §8.11 with §23.9: inside a method a bare name is the object's property
// ahead of a variable of the module the class is declared in; only a local
// of the method's own shadows it. Deferring to any variable of the name,
// `d = new[2]` in a method sized the module's `d` and left the property
// empty. §8.10: a static method has no object, and names its class's static
// properties bare.
static bool ResolveBareClassArray(const Expr* base, SimContext& ctx,
                                  ClassArrayRef& out) {
  if (ctx.FindLocalVariable(base->text) != nullptr) return false;
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* type =
      self != nullptr ? self->type : ctx.CurrentMethodClass();
  if (type == nullptr) return false;
  const auto* prop = FindClassArrayProperty(type, base->text);
  if (prop == nullptr || (self == nullptr && !prop->is_static)) return false;
  out = MakeRef(self, type, prop, /*bare=*/true);
  // 18.5.7.1: a constraint's trial binds a dynamic array's size as it binds
  // its elements, so the size is the local's where one is in scope.
  if (auto* size = ctx.FindVariable(ClassArraySizeKey(base->text)))
    out.size = static_cast<uint32_t>(size->value.ToUint64());
  return true;
}

// §8.23: `C::sarr` names the static property of class C.
static bool ResolveScopedClassArray(const Expr* base, SimContext& ctx,
                                    ClassArrayRef& out) {
  if (base->lhs->kind != ExprKind::kIdentifier) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(base->lhs->text);
  if (cls == nullptr) return false;
  const auto* prop = FindClassArrayProperty(cls, base->rhs->text);
  if (prop == nullptr || !prop->is_static) return false;
  out = MakeRef(nullptr, cls, prop, /*bare=*/false);
  return true;
}

// §7.4.2 with §7.4.4 and §8.5: `g[1]` of a property with more than one
// unpacked dimension, `int g[2][3]`, is a subarray, an array of the next
// dimension whose elements are held under keys extending its own, `g[1][2]`.
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
  out = outer;
  out.path =
      ClassArrayRefElementKey(outer, static_cast<int64_t>(idx.ToUint64()));
  out.dim = outer.dim + 1;
  out.lo = outer.prop->dim_los[out.dim];
  out.size = outer.prop->dim_sizes[out.dim];
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
  if (base->is_scope_resolution) return ResolveScopedClassArray(base, ctx, out);
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return false;
  const auto* prop = FindClassArrayProperty(obj->type, base->rhs->text);
  if (prop == nullptr) return false;
  out = MakeRef(obj, obj->type, prop, /*bare=*/false);
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
  uint64_t acc = 0;
  if (!ReductionIdentity(method, acc)) return false;
  out = ReduceClassArray(expr, ref, method, ctx, arena);
  return true;
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

// Selected as the property's own element, `h.inst[0]`, the select named no
// array property and the write went nowhere.
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
  int64_t size = SignExtend(size_val.ToUint64(), size_val.width);
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
  return true;
}

// The declared index of the i-th element from the left of `ref`, the higher
// bound first for a descending dimension (§7.4.2).
static int64_t IndexFromLeft(const ClassArrayRef& ref, uint32_t i) {
  return ref.prop->array_descending
             ? ref.lo + static_cast<int64_t>(ref.size) - 1 - i
             : ref.lo + i;
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

// §7.6 with §7.10: `lhs`, a queue property, rebuilt from `elems`.
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

// §10.9.1 with §7.5: the element count the positional pattern `rhs` gives a
// dynamic array assigned it -- its items, a replication `'{3{7, 8}}` counted
// as many times as it says -- into `out`; false for a keyed pattern, which
// names no count, and for a replication whose count is unknown.
static bool PatternItemCount(const Expr* rhs, SimContext& ctx, Arena& arena,
                             uint32_t& out) {
  if (!rhs->pattern_keys.empty()) return false;
  out = static_cast<uint32_t>(rhs->elements.size());
  if (out != 1 || rhs->elements[0]->kind != ExprKind::kReplicate) return true;
  const Expr* rep = rhs->elements[0];
  Logic4Vec count = EvalExpr(rep->repeat_count, ctx, arena);
  if (!count.IsKnown()) return false;
  out = static_cast<uint32_t>(count.ToUint64() * rep->elements.size());
  return true;
}

bool StoreClassArrayPattern(const ClassArrayRef& dst_ref, const Expr* rhs,
                            SimContext& ctx, Arena& arena) {
  if (rhs == nullptr || rhs->kind != ExprKind::kAssignmentPattern ||
      ClassArrayHoldsSubarrays(dst_ref)) {
    return false;
  }
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
  if (lhs == nullptr || (lhs->kind != ExprKind::kIdentifier &&
                         lhs->kind != ExprKind::kMemberAccess)) {
    return false;
  }
  if (stmt->rhs != nullptr && stmt->rhs->kind == ExprKind::kAssignmentPattern) {
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
