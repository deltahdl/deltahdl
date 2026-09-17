#include "simulator/eval_class_array.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

std::string ClassArrayElementKey(std::string_view name, int64_t index) {
  return std::string(name) + "[" + std::to_string(index) + "]";
}

const ClassTypeInfo::PropertyInfo* FindClassArrayProperty(
    const ClassTypeInfo* type, std::string_view name) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name == name) return prop.array_size > 0 ? &prop : nullptr;
    }
  }
  return nullptr;
}

namespace {

// The object a member access's handle side names: the running method's object
// for `this`, else the object the handle the side evaluates to refers to.
ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena) {
  if (side->kind == ExprKind::kIdentifier && side->text == "this")
    return ctx.CurrentThis();
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

// Whether `index` addresses an element of `prop`.
bool IndexInRange(const ClassTypeInfo::PropertyInfo& prop, int64_t index) {
  return index >= prop.array_lo &&
         index < prop.array_lo + static_cast<int64_t>(prop.array_size);
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

}  // namespace

bool ResolveClassArray(const Expr* base, SimContext& ctx, Arena& arena,
                       ClassArrayRef& out) {
  if (base == nullptr) return false;
  if (base->kind == ExprKind::kIdentifier) {
    if (ctx.FindVariable(base->text) != nullptr ||
        ctx.FindArrayInfo(base->text) != nullptr) {
      return false;
    }
    ClassObject* self = ctx.CurrentThis();
    if (self == nullptr) return false;
    const auto* prop = FindClassArrayProperty(self->type, base->text);
    if (prop == nullptr) return false;
    out = {self, prop, /*bare=*/true};
    return true;
  }
  if (base->kind != ExprKind::kMemberAccess || base->is_scope_resolution ||
      base->lhs == nullptr || base->rhs == nullptr ||
      base->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return false;
  const auto* prop = FindClassArrayProperty(obj->type, base->rhs->text);
  if (prop == nullptr) return false;
  out = {obj, prop, /*bare=*/false};
  return true;
}

Logic4Vec ReadClassArrayElement(const ClassArrayRef& ref, int64_t index,
                                SimContext& ctx, Arena& arena) {
  if (!IndexInRange(*ref.prop, index)) {
    return ref.prop->is_4state ? MakeAllX(arena, ref.prop->width)
                               : MakeLogic4VecVal(arena, ref.prop->width, 0);
  }
  std::string key = ClassArrayElementKey(ref.prop->name, index);
  if (ref.bare) {
    if (auto* local = ctx.FindVariable(key)) return local->value;
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
  if (receiver == nullptr || expr->with_expr != nullptr) return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(receiver, ctx, arena, ref)) return false;
  if (method == "size") {
    out = MakeLogic4VecVal(arena, 32, ref.prop->array_size);
    return true;
  }
  uint64_t acc = 0;
  if (!ReductionIdentity(method, acc)) return false;
  for (uint32_t i = 0; i < ref.prop->array_size; ++i) {
    acc = Join(method, acc,
               ReadClassArrayElement(ref, ref.prop->array_lo + i, ctx, arena)
                   .ToUint64());
  }
  // §7.12.3: the result is of the element type, which the fold is held to.
  out = MakeLogic4VecVal(arena, ref.prop->width, acc);
  out.is_signed = ref.prop->is_signed;
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
  auto index = static_cast<int64_t>(idx_val.ToUint64());
  if (!IndexInRange(*ref.prop, index)) return true;
  Logic4Vec stored =
      CoerceToPropertyType(ref.obj->type, ref.prop->name, rhs_val, arena);
  ref.obj->SetProperty(ClassArrayElementKey(ref.prop->name, index), stored);
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
  return true;
}

}  // namespace delta
