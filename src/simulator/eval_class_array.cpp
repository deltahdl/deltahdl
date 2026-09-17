#include "simulator/eval_class_array.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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

const ClassTypeInfo::PropertyInfo* FindClassArrayProperty(
    const ClassTypeInfo* type, std::string_view name) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name == name) return prop.IsArray() ? &prop : nullptr;
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

// The reference `obj` and `prop` make, with the elements the object holds.
ClassArrayRef MakeRef(ClassObject* obj, const ClassTypeInfo::PropertyInfo* prop,
                      bool bare) {
  ClassArrayRef ref{obj, prop, bare, ClassArraySize(obj, *prop),
                    prop->is_dynamic ? 0 : prop->array_lo};
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
    out = MakeRef(self, prop, /*bare=*/true);
    // 18.5.7.1: a constraint's trial binds a dynamic array's size as it binds
    // its elements, so the size is the local's where one is in scope.
    if (auto* size = ctx.FindVariable(ClassArraySizeKey(base->text)))
      out.size = static_cast<uint32_t>(size->value.ToUint64());
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
  out = MakeRef(obj, prop, /*bare=*/false);
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
    ref.obj->SetProperty(ClassArrayElementKey(ref.prop->name, i), val);
  }
  ref.obj->SetProperty(ClassArraySizeKey(ref.prop->name),
                       MakeLogic4VecVal(arena, 32, size));
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
}

Logic4Vec ReadClassArrayElement(const ClassArrayRef& ref, int64_t index,
                                SimContext& ctx, Arena& arena) {
  if (!IndexInRange(ref, index)) return ElementDefault(*ref.prop, arena);
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
  auto index = static_cast<int64_t>(idx_val.ToUint64());
  if (!IndexInRange(ref, index)) return true;
  Logic4Vec stored =
      CoerceToPropertyType(ref.obj->type, ref.prop->name, rhs_val, arena);
  ref.obj->SetProperty(ClassArrayElementKey(ref.prop->name, index), stored);
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
  return true;
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

}  // namespace delta
