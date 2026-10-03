#include "simulator/virtual_interface.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_hier.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

bool DeclaresAVirtualInterface(const DataType& type, const SimContext& ctx) {
  if (type.kind == DataTypeKind::kVirtualInterface) return true;
  if (type.kind != DataTypeKind::kNamed) return false;
  // The key the elaborated table records a typedef under, which
  // DeclaredTypeWidth in evaluation_literal.cpp forms the same way: the bare
  // name, or `scope::name` for one reached through a package or class scope.
  std::string key =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  return ctx.FindTypeKind(key) == DataTypeKind::kVirtualInterface;
}

// §8.10: a static property is the class's own, read from the class that
// declares it whichever class the running method belongs to.
static uint64_t StaticPropertyHandle(const ClassTypeInfo* scope,
                                     std::string_view name) {
  for (const auto* t = scope; t != nullptr; t = t->parent) {
    auto it = t->static_properties.find(std::string(name));
    if (it != t->static_properties.end()) return it->second.ToUint64();
  }
  return kNullVirtualInterface;
}

// §8.15: an instance property is read against the class the running method is
// defined in, so a base method reads the base declaration even where a derived
// class shadows the name, as EvalIdentifierClassScope in evaluation.cpp reads
// any other property by its bare name. With no such class, `name` is read
// against the object's own type, which is how a property of an object reached
// through a handle is read.
static uint64_t InstancePropertyHandle(const ClassObject* self,
                                       const ClassTypeInfo* method_cls,
                                       std::string_view name, Arena& arena) {
  if (self == nullptr) return kNullVirtualInterface;
  Logic4Vec held = method_cls != nullptr
                       ? self->GetPropertyForType(name, method_cls, arena)
                       : self->GetProperty(name, arena);
  return held.ToUint64();
}

// §25.9: the property `name` of `scope`, when the class declares it a virtual
// interface: static ones read from the class, instance ones from `self`
// against `method_cls`.
static VirtualInterfaceBase PropertyBase(const ClassTypeInfo* scope,
                                         const ClassObject* self,
                                         const ClassTypeInfo* method_cls,
                                         std::string_view name, Arena& arena) {
  VirtualInterfaceBase base;
  if (scope == nullptr) return base;
  const ClassTypeInfo::PropertyInfo* prop = scope->FindProperty(name);
  if (prop == nullptr || !prop->is_virtual_interface) return base;
  base.is_virtual_interface = true;
  base.handle = prop->is_static
                    ? StaticPropertyHandle(scope, name)
                    : InstancePropertyHandle(self, method_cls, name, arena);
  return base;
}

VirtualInterfaceBase ResolveVirtualInterfaceBase(std::string_view name,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  VirtualInterfaceBase base;
  if (const Variable* var = ctx.FindVariable(name); var != nullptr) {
    base.is_virtual_interface = var->is_virtual_interface;
    if (base.is_virtual_interface) base.handle = var->value.ToUint64();
    return base;
  }
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  const ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* scope = method_cls != nullptr ? method_cls
                               : self != nullptr     ? self->type
                                                     : nullptr;
  return PropertyBase(scope, self, method_cls, name, arena);
}

// §8.3: whether property `name` of `type` is declared with a class type and
// so holds a handle to an object. A virtual interface property holds a handle
// of another kind, issued from another table, and a structure-typed property
// holds a value, so neither denotes an object whatever its value is.
static bool HoldsAClassHandle(const ClassTypeInfo* type, std::string_view name,
                              SimContext& ctx) {
  std::string_view class_name = MemberClassTypeName(type, name);
  return !class_name.empty() && ctx.FindClassType(class_name) != nullptr;
}

// §8.3: the object a bare name denotes when it holds a class handle: `this`
// is the object the running method runs on (§8.11); a variable of the running
// scope declared with a class type holds a handle to one; and, where no
// variable answers the name, a class-typed property of the running method's
// object does. A virtual interface holds a handle of another kind, so a name
// declared so denotes no object here, whatever its value.
static const ClassObject* ObjectOfName(std::string_view name, SimContext& ctx,
                                       Arena& arena) {
  // §8.15: `super` denotes the same object, its members looked up from the
  // base of the running method's class (ResolveVirtualInterfaceBaseExpr).
  if (name == "this" || name == "super") return ctx.CurrentThis();
  if (const Variable* var = ctx.FindVariable(name); var != nullptr) {
    if (var->is_virtual_interface || ctx.GetVariableClassType(name).empty())
      return nullptr;
    return ctx.GetClassObject(var->value.ToUint64());
  }
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr || !HoldsAClassHandle(self->type, name, ctx))
    return nullptr;
  return ctx.GetClassObject(
      InstancePropertyHandle(self, ctx.CurrentMethodClass(), name, arena));
}

// §8.3: the object an expression denotes when it holds a class handle: a
// bare name as ObjectOfName reads it, or a member access `h.p` with `h` an
// object and `p` a class-typed property of it, followed as deep as the
// expression goes. nullptr for an expression of any other shape, for a
// property that is no class handle, and for a null handle.
static const ClassObject* ObjectOf(const Expr* e, SimContext& ctx,
                                   Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier)
    return ObjectOfName(e->text, ctx, arena);
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution ||
      e->rhs == nullptr || e->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  const ClassObject* holder = ObjectOf(e->lhs, ctx, arena);
  if (holder == nullptr || !HoldsAClassHandle(holder->type, e->rhs->text, ctx))
    return nullptr;
  return ctx.GetClassObject(
      InstancePropertyHandle(holder, nullptr, e->rhs->text, arena));
}

// §7 with §25.9: the element `select` picks out of a container whose
// elements are virtual interfaces holds the handle of the instance it
// represents, read by evaluating the select; an element holding an unknown
// bit represents none.
static VirtualInterfaceBase SelectedElementBase(const Expr* select,
                                                SimContext& ctx, Arena& arena) {
  if (select->index_end != nullptr) return {};
  const Expr* container = select->base;
  while (container != nullptr && container->kind == ExprKind::kSelect)
    container = container->base;
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(container, ctx, arena);
  if (!base.is_virtual_interface) return base;
  Logic4Vec element = EvalExpr(select, ctx, arena);
  base.handle = element.IsKnown() ? element.ToUint64() : kNullVirtualInterface;
  return base;
}

// §8.23: `C::p` names the static property p of the class C, which a
// virtual interface declared so holds once for the class.
static VirtualInterfaceBase ClassScopedBase(const Expr* base, SimContext& ctx,
                                            Arena& arena) {
  if (base->lhs == nullptr || base->lhs->kind != ExprKind::kIdentifier ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  const ClassTypeInfo* cls = ctx.FindClassType(base->lhs->text);
  return PropertyBase(cls, nullptr, nullptr, base->rhs->text, arena);
}

VirtualInterfaceBase ResolveVirtualInterfaceBaseExpr(const Expr* base,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  if (base == nullptr) return {};
  if (base->kind == ExprKind::kIdentifier) {
    return ResolveVirtualInterfaceBase(base->text, ctx, arena);
  }
  if (base->kind == ExprKind::kSelect) {
    return SelectedElementBase(base, ctx, arena);
  }
  if (base->kind == ExprKind::kMemberAccess && base->is_scope_resolution) {
    return ClassScopedBase(base, ctx, arena);
  }
  if (base->kind != ExprKind::kMemberAccess || base->is_scope_resolution ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  const ClassObject* holder = ObjectOf(base->lhs, ctx, arena);
  if (holder == nullptr) return {};
  // §8.15: `this.p` names the property as the running method's class
  // declares it, which is what a bare `p` in the same method names; a
  // property of any other object is read against that object's own type.
  // `super.p` names it as the base of that class declares it, and read
  // against the running method's class instead, `super.vif.a` found no
  // `vif` and read 0 where `this.vif.a` read the member.
  const ClassTypeInfo* method_cls =
      holder == ctx.CurrentThis() ? ctx.CurrentMethodClass() : nullptr;
  if (method_cls != nullptr && base->lhs->kind == ExprKind::kIdentifier &&
      base->lhs->text == "super" && method_cls->parent != nullptr) {
    method_cls = method_cls->parent;
  }
  const ClassTypeInfo* scope =
      method_cls != nullptr ? method_cls : holder->type;
  return PropertyBase(scope, holder, method_cls, base->rhs->text, arena);
}

VirtualInterfaceBase ResolveVirtualInterfaceInnerPath(const Expr* expr,
                                                      SimContext& ctx,
                                                      Arena& arena,
                                                      std::string& field) {
  for (const Expr* node = expr->lhs;
       node != nullptr && node->kind == ExprKind::kMemberAccess &&
       !node->is_scope_resolution;
       node = node->lhs) {
    VirtualInterfaceBase base =
        ResolveVirtualInterfaceBaseExpr(node->lhs, ctx, arena);
    if (!base.is_virtual_interface) continue;
    std::string full = HierarchicalReferenceName(expr);
    std::string head = HierarchicalReferenceName(node->lhs) + ".";
    if (!full.starts_with(head)) return {};
    field = full.substr(head.size());
    return base;
  }
  return {};
}

std::string VirtualInterfaceComponentName(uint64_t handle,
                                          std::string_view field,
                                          const SimContext& ctx) {
  std::string_view scope = ctx.VirtualInterfaceScope(handle);
  if (scope.empty()) return {};
  std::string name(scope);
  name += ".";
  name += field;
  return name;
}

uint64_t VirtualInterfaceOperandHandle(const Expr* operand, SimContext& ctx,
                                       Arena& arena) {
  if (operand == nullptr) return kNullVirtualInterface;
  if (operand->kind == ExprKind::kIdentifier && operand->text == "null" &&
      ctx.FindVariable(operand->text) == nullptr) {
    return kNullVirtualInterface;
  }
  return EvalExpr(operand, ctx, arena).ToUint64();
}

// Whether the path `expr` starts at a name that holds storage of the running
// scope rather than at an instance, a generate block or a top: a variable,
// an array, a net or a property of the class whose method is running.
static bool PathHeadHoldsStorage(const Expr* expr, SimContext& ctx) {
  const Expr* head = expr;
  while (head != nullptr && (head->kind == ExprKind::kSelect ||
                             head->kind == ExprKind::kMemberAccess)) {
    head = head->kind == ExprKind::kSelect ? head->base : head->lhs;
  }
  if (head == nullptr || head->kind != ExprKind::kIdentifier) return true;
  return ctx.FindVariable(head->text) != nullptr ||
         ctx.FindArrayInfo(head->text) != nullptr ||
         ctx.FindNet(head->text) != nullptr ||
         ClassScopeDeclares(head->text, ctx);
}

bool TryInterfaceInstancePathHandle(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  if (PathHeadHoldsStorage(expr, ctx)) return false;
  std::string path = EvaluatedHierarchicalPath(expr, ctx, arena);
  if (path.empty()) return false;
  std::string scope = ctx.ResolveInstanceScope(path);
  if (scope.empty()) return false;
  out = MakeLogic4VecVal(arena, 64, ctx.VirtualInterfaceHandle(scope));
  return true;
}

void ReportNullVirtualInterface(SourceLoc loc, SimContext& ctx) {
  ctx.GetDiag().Error(loc, "reference through a null virtual interface",
                      Subclause("25.9"));
  ctx.RequestFinish();
}

}  // namespace delta
