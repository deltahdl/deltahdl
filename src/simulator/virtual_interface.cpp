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
  std::string key =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  return ctx.FindTypeKind(key) == DataTypeKind::kVirtualInterface;
}

static uint64_t StaticPropertyHandle(const ClassTypeInfo* scope,
                                     std::string_view name) {
  for (const auto* t = scope; t != nullptr; t = t->parent) {
    auto it = t->static_properties.find(std::string(name));
    if (it != t->static_properties.end()) return it->second.ToUint64();
  }
  return kNullVirtualInterface;
}

static uint64_t InstancePropertyHandle(const ClassObject* self,
                                       const ClassTypeInfo* method_cls,
                                       std::string_view name, Arena& arena) {
  if (self == nullptr) return kNullVirtualInterface;
  Logic4Vec held = method_cls != nullptr
                       ? self->GetPropertyForType(name, method_cls, arena)
                       : self->GetProperty(name, arena);
  return held.ToUint64();
}

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

static bool NamesAContainer(std::string_view name, SimContext& ctx) {
  return ctx.FindArrayInfo(name) != nullptr || ctx.FindQueue(name) != nullptr ||
         ctx.FindAssocArray(name) != nullptr;
}

VirtualInterfaceBase ResolveVirtualInterfaceBase(std::string_view name,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  VirtualInterfaceBase base;
  if (const Variable* var = ctx.FindVariable(name); var != nullptr) {
    base.is_virtual_interface =
        var->is_virtual_interface && !NamesAContainer(name, ctx);
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

static bool HoldsAClassHandle(const ClassTypeInfo* type, std::string_view name,
                              SimContext& ctx) {
  std::string_view class_name = MemberClassTypeName(type, name);
  return !class_name.empty() && ctx.FindClassType(class_name) != nullptr;
}

static const ClassObject* ObjectOfName(std::string_view name, SimContext& ctx,
                                       Arena& arena) {
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

static VirtualInterfaceBase SelectedElementBase(const Expr* select,
                                                SimContext& ctx, Arena& arena) {
  if (select->index_end != nullptr) return {};
  const Expr* container = select->base;
  while (container != nullptr && container->kind == ExprKind::kSelect)
    container = container->base;
  VirtualInterfaceBase base;
  const Variable* var =
      container != nullptr && container->kind == ExprKind::kIdentifier
          ? ctx.FindVariable(container->text)
          : nullptr;
  base.is_virtual_interface =
      var != nullptr ? var->is_virtual_interface
                     : ResolveVirtualInterfaceBaseExpr(container, ctx, arena)
                           .is_virtual_interface;
  if (!base.is_virtual_interface) return base;
  Logic4Vec element = EvalExpr(select, ctx, arena);
  base.handle = element.IsKnown() ? element.ToUint64() : kNullVirtualInterface;
  return base;
}

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
