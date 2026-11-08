#include "simulator/eval_array_class_assoc.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_element_assoc.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

const DataType* TypeParamActual(const ClassObject* obj, const ClassDecl* decl,
                                std::string_view pname) {
  if (obj != nullptr) {
    auto it = obj->type_param_actuals.find(std::string(pname));
    if (it != obj->type_param_actuals.end()) return it->second;
  }
  for (size_t i = 0; i < decl->params.size() && i < decl->param_types.size();
       ++i) {
    if (decl->params[i].first == pname) return &decl->param_types[i];
  }
  return nullptr;
}

namespace {

struct PropertyDeclaration {
  const ClassMember* member = nullptr;
  const ClassTypeInfo* declaring = nullptr;
};

PropertyDeclaration FindPropertyDeclaration(const ClassTypeInfo* from,
                                            std::string_view field) {
  for (const auto* t = from; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == field)
        return {m, t};
    }
  }
  return {};
}

}  // namespace

std::string_view TypeParamNamedBy(const ClassDecl* decl,
                                  std::string_view name) {
  if (decl->type_param_names.count(name) != 0) return name;
  for (const auto* m : decl->members) {
    if (m->kind != ClassMemberKind::kTypedef || m->name != name ||
        m->typedef_item == nullptr)
      continue;
    const DataType& t = m->typedef_item->typedef_type;
    bool bare = t.kind == DataTypeKind::kNamed && t.scope_name.empty() &&
                t.packed_dim_left == nullptr && t.extra_packed_dims.empty() &&
                t.type_params.empty() && m->typedef_item->unpacked_dims.empty();
    if (bare && decl->type_param_names.count(t.type_name) != 0)
      return t.type_name;
    return {};
  }
  return {};
}

std::string_view PropertyClassName(const ClassObject* obj,
                                   const ClassTypeInfo* from,
                                   std::string_view field, SimContext& ctx) {
  PropertyDeclaration decl = FindPropertyDeclaration(from, field);
  if (decl.member == nullptr) return {};
  Arena& arena = ctx.GetArena();
  std::string_view key = DeclaredClassKeyInScope(decl.member->data_type,
                                                 decl.declaring, ctx, arena);
  if (!key.empty()) return key;
  std::string_view name = decl.member->data_type.type_name;
  const ClassDecl* cls = decl.declaring->decl;
  if (name.empty() || cls->type_param_names.count(name) == 0) return {};
  const DataType* bound = TypeParamActual(obj, cls, name);
  if (bound == nullptr || bound->kind != DataTypeKind::kNamed) return {};
  return DeclaredClassKeyInScope(*bound, decl.declaring, ctx, arena);
}

bool PropertyIsArray(const ClassTypeInfo* from, std::string_view field,
                     SimContext& ctx) {
  PropertyDeclaration decl = FindPropertyDeclaration(from, field);
  if (decl.member == nullptr) return false;
  return !decl.member->unpacked_dims.empty() ||
         PropertyTypedefItem(decl.member, decl.declaring, ctx) != nullptr;
}

bool IsHandlePath(const Expr* expr) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) return true;
  if (expr->kind == ExprKind::kCall) return StartsAtHeldCall(expr);
  return expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution &&
         expr->rhs != nullptr && expr->rhs->kind == ExprKind::kIdentifier &&
         IsHandlePath(expr->lhs);
}

ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena) {
  if (!IsHandlePath(side)) return nullptr;
  if (side->kind == ExprKind::kIdentifier && side->text == "this")
    return ctx.CurrentThis();
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

std::string InstanceMemberKey(const Expr* access) {
  if (access == nullptr) return {};
  if (access->kind == ExprKind::kIdentifier) return std::string(access->text);
  if (access->kind != ExprKind::kMemberAccess || access->is_scope_resolution ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string prefix = InstanceMemberKey(access->lhs);
  if (prefix.empty()) return {};
  return prefix + "." + std::string(access->rhs->text);
}

static const ModuleItem* OwnTypedefItem(const ClassTypeInfo* t,
                                        std::string_view name) {
  if (t->decl == nullptr) return nullptr;
  for (const ClassMember* m : t->decl->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == name)
      return m->typedef_item;
  }
  return nullptr;
}

const ModuleItem* ClassScopeTypedefItem(const ClassTypeInfo* from,
                                        std::string_view name) {
  for (const ClassTypeInfo* scope = from; scope != nullptr;
       scope = scope->enclosing) {
    for (const ClassTypeInfo* t = scope; t != nullptr; t = t->parent) {
      if (const ModuleItem* item = OwnTypedefItem(t, name)) return item;
    }
  }
  return nullptr;
}

const ModuleItem* TypedefItemSeenFrom(const DataType& type,
                                      const ClassTypeInfo* from,
                                      SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return nullptr;
  std::string_view name = type.type_name;
  if (!type.scope_name.empty()) {
    if (const ClassTypeInfo* cls = ctx.FindClassType(type.scope_name))
      return ClassScopeTypedefItem(cls, name);
    return ctx.FindTypedefItem(std::string(type.scope_name) +
                               "::" + std::string(name));
  }
  if (const ModuleItem* item = ClassScopeTypedefItem(from, name)) return item;
  if (from != nullptr && !from->package.empty()) {
    if (const ModuleItem* item = ctx.FindTypedefItem(
            std::string(from->package) + "::" + std::string(name))) {
      return item;
    }
  }
  return ctx.FindTypedefItem(name);
}

static const DataType* SpecializationTypeActual(const ClassTypeInfo* declaring,
                                                std::string_view name) {
  const ClassDecl* decl = declaring->decl;
  if (declaring->param_actuals != nullptr) {
    for (size_t i = 0; i < decl->params.size(); ++i) {
      if (decl->params[i].first != name) continue;
      if (const DataType* actual =
              ActualForParam(*declaring->param_actuals, i, name)) {
        return actual;
      }
    }
  }
  return TypeParamActual(nullptr, decl, name);
}

static const DataType* PropertyWrittenType(const ClassMember* member,
                                           const ClassTypeInfo* declaring) {
  const DataType& type = member->data_type;
  if (declaring == nullptr || declaring->decl == nullptr ||
      type.kind != DataTypeKind::kNamed || !type.scope_name.empty() ||
      declaring->decl->type_param_names.count(type.type_name) == 0) {
    return &type;
  }
  return SpecializationTypeActual(declaring, type.type_name);
}

const ModuleItem* PropertyNamedTypedef(const ClassMember* member,
                                       const ClassTypeInfo* declaring,
                                       SimContext& ctx) {
  if (!member->unpacked_dims.empty()) return nullptr;
  const DataType* type = PropertyWrittenType(member, declaring);
  if (type == nullptr) return nullptr;
  return TypedefItemSeenFrom(*type, declaring, ctx);
}

const ModuleItem* PropertyTypedefItem(const ClassMember* member,
                                      const ClassTypeInfo* declaring,
                                      SimContext& ctx) {
  const ModuleItem* item = PropertyNamedTypedef(member, declaring, ctx);
  if (item == nullptr || item->unpacked_dims.empty()) return nullptr;
  return item;
}

const Stmt* DeclShapedByTypedef(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  const DataType& type = stmt->var_decl_type;
  if (type.kind != DataTypeKind::kNamed) return stmt;
  auto& shaped_decls = ctx.ClassTypedefShapedDecls();
  if (!stmt->var_unpacked_dims.empty()) {
    auto reshaped = shaped_decls.find(stmt);
    return reshaped == shaped_decls.end() ? stmt : reshaped->second;
  }
  auto [it, fresh] = shaped_decls.try_emplace(stmt, stmt);
  if (!fresh) return it->second;
  const ClassTypeInfo* from = nullptr;
  if (!type.scope_name.empty()) {
    from = ctx.FindClassType(type.scope_name);
  } else {
    from = ctx.CurrentMethodClass();
    if (from == nullptr && ctx.CurrentThis() != nullptr) {
      from = ctx.CurrentThis()->type;
    }
  }
  const ModuleItem* item = TypedefItemSeenFrom(type, from, ctx);
  if (item == nullptr || item->unpacked_dims.empty()) return stmt;
  auto* shaped = arena.Create<Stmt>(*stmt);
  shaped->var_decl_type = item->typedef_type;
  shaped->var_decl_type.is_const = type.is_const;
  shaped->var_unpacked_dims = item->unpacked_dims;
  it->second = shaped;
  return shaped;
}

namespace {

bool DimNamesTypeParam(const Expr* dim, const ClassDecl* decl) {
  return dim != nullptr && dim->kind == ExprKind::kIdentifier &&
         decl->type_param_names.count(dim->text) != 0;
}

const std::vector<Expr*>& PropertyUnpackedDims(const ClassMember* member,
                                               const ClassTypeInfo* declaring,
                                               SimContext& ctx) {
  const ModuleItem* item = PropertyTypedefItem(member, declaring, ctx);
  return item != nullptr ? item->unpacked_dims : member->unpacked_dims;
}

bool DeclaresAssocProperty(const ClassMember* member,
                           const ClassTypeInfo* declaring, SimContext& ctx) {
  const std::vector<Expr*>& dims = PropertyUnpackedDims(member, declaring, ctx);
  if (member->is_param || dims.size() != 1) return false;
  const Expr* dim = dims[0];
  return IsAssocIndexDim(dim, ctx) || DimNamesTypeParam(dim, declaring->decl);
}

const ClassMember* FindAssocPropertyDecl(const ClassTypeInfo* type,
                                         std::string_view name, SimContext& ctx,
                                         const ClassTypeInfo*& declaring) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* member : t->decl->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name)
        continue;
      if (!DeclaresAssocProperty(member, t, ctx)) return nullptr;
      declaring = t;
      return member;
    }
  }
  return nullptr;
}

DataType ResolveNamedType(const DataType& type) {
  if (type.kind != DataTypeKind::kImplicit || type.type_ref_expr == nullptr ||
      type.type_ref_expr->kind != ExprKind::kIdentifier) {
    return type;
  }
  return TypeNameToDataType(type.type_ref_expr->text);
}

DataType PropertyIndexType(const ClassMember* member,
                           const ClassTypeInfo* declaring,
                           const ClassObject* obj, SimContext& ctx) {
  const ClassDecl* decl = declaring->decl;
  const Expr* dim = PropertyUnpackedDims(member, declaring, ctx)[0];
  if (!DimNamesTypeParam(dim, decl)) return AssocIndexType(dim, ctx);
  const DataType* bound = TypeParamActual(obj, decl, dim->text);
  DataType index_type =
      bound != nullptr ? ResolveNamedType(*bound) : TypeNameToDataType("int");
  if (index_type.kind == DataTypeKind::kImplicit)
    index_type = TypeNameToDataType("int");
  return index_type;
}

AssocArraySpec PropertyIndexSpec(const ClassMember* member,
                                 const ClassTypeInfo* declaring,
                                 const ClassObject* obj, bool elem_4state,
                                 SimContext& ctx) {
  const Expr* dim = PropertyUnpackedDims(member, declaring, ctx)[0];
  if (!DimNamesTypeParam(dim, declaring->decl))
    return AssocIndexSpec(dim, elem_4state, ctx);
  return AssocIndexSpecOfType(PropertyIndexType(member, declaring, obj, ctx),
                              elem_4state, ctx);
}

AssocArrayObject* MakeAssocProperty(const ClassTypeInfo* declaring,
                                    const ClassMember* member,
                                    const ClassObject* obj, SimContext& ctx) {
  static const ClassTypeInfo::PropertyInfo kNoProperty;
  const auto* found = declaring->FindProperty(member->name);
  const auto& prop = found != nullptr ? *found : kNoProperty;
  uint32_t elem_width = prop.width;
  bool elem_4state = prop.is_4state;
  AssocArraySpec spec =
      PropertyIndexSpec(member, declaring, obj, elem_4state, ctx);
  auto* aa = ctx.GetArena().Create<AssocArrayObject>();
  aa->elem_width = elem_width;
  aa->is_string_key = PropertyIndexType(member, declaring, obj, ctx).kind ==
                      DataTypeKind::kString;
  aa->is_wildcard = spec.is_wildcard;
  aa->index_width = spec.index_width;
  aa->is_4state = spec.is_4state;
  aa->is_signed = prop.is_signed;
  aa->is_index_signed = spec.is_index_signed;
  aa->index_class = spec.index_class;
  aa->index_type_name = spec.index_type_name;
  aa->elem_class = PropertyClassName(obj, declaring, member->name, ctx);
  return aa;
}

AssocArrayObject* ResolveOn(ClassObject* obj, const ClassTypeInfo* from,
                            std::string_view name, SimContext& ctx,
                            ClassObject** owner) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = FindAssocPropertyDecl(from, name, ctx, declaring);
  if (member == nullptr) return nullptr;
  if (member->is_static) {
    auto& slot = declaring->static_assoc_properties[std::string(name)];
    if (slot == nullptr)
      slot = MakeAssocProperty(declaring, member, nullptr, ctx);
    return slot;
  }
  if (obj == nullptr) return nullptr;
  const ClassTypeInfo* nearest = nullptr;
  FindAssocPropertyDecl(obj->type, name, ctx, nearest);
  std::string key =
      nearest == declaring || declaring == nullptr
          ? std::string(name)
          : std::string(declaring->name) + "::" + std::string(name);
  auto& slot = obj->assoc_properties[key];
  if (slot == nullptr) slot = MakeAssocProperty(declaring, member, obj, ctx);
  if (owner != nullptr) *owner = obj;
  return slot;
}

AssocArrayObject* ScopeResolvedAssocProperty(const Expr* base,
                                             SimContext& ctx) {
  if (base->lhs == nullptr || base->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  std::string key =
      std::string(base->lhs->text) + "." + std::string(base->rhs->text);
  if (auto* aa = ctx.FindAssocArray(key)) return aa;
  const ClassTypeInfo* cls = ctx.FindClassType(base->lhs->text);
  if (cls == nullptr) return nullptr;
  return ResolveOn(nullptr, cls, base->rhs->text, ctx, nullptr);
}

}  // namespace

bool IsAssocPropertyDecl(const ClassMember* member,
                         const ClassTypeInfo* declaring, SimContext& ctx) {
  return DeclaresAssocProperty(member, declaring, ctx);
}

AssocArrayObject* ClassAssocProperty(ClassObject* obj,
                                     const ClassTypeInfo* from,
                                     std::string_view name, SimContext& ctx) {
  return ResolveOn(obj, from, name, ctx, nullptr);
}

AssocArrayObject* FindAssocArrayOfName(std::string_view name, SimContext& ctx,
                                       ClassObject** owner) {
  if (owner != nullptr) *owner = nullptr;
  if (auto* aa = ctx.FindAssocArray(name)) return aa;
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  if (from == nullptr && self != nullptr) from = self->type;
  if (from == nullptr) return nullptr;
  if (ctx.FindVariable(name) != nullptr || ctx.FindQueue(name) != nullptr ||
      ctx.FindArrayInfo(name) != nullptr) {
    return nullptr;
  }
  return ResolveOn(self, from, name, ctx, owner);
}

AssocArrayObject* FindAssocArrayOfBase(const Expr* base, SimContext& ctx,
                                       Arena& arena, ClassObject** owner) {
  if (owner != nullptr) *owner = nullptr;
  if (base == nullptr) return nullptr;
  if (base->kind == ExprKind::kIdentifier)
    return FindAssocArrayOfName(base->text, ctx, owner);
  if (base->kind == ExprKind::kSelect)
    return ElementAssocOfSelect(base, ctx, arena, false);
  if (base->kind != ExprKind::kMemberAccess || base->lhs == nullptr ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (base->is_scope_resolution) return ScopeResolvedAssocProperty(base, ctx);
  if (base->lhs->kind == ExprKind::kIdentifier && base->lhs->text == "super") {
    const ClassTypeInfo* cls = ctx.CurrentMethodClass();
    if (ctx.CurrentThis() == nullptr || cls == nullptr ||
        cls->parent == nullptr)
      return nullptr;
    return ResolveOn(ctx.CurrentThis(), cls->parent, base->rhs->text, ctx,
                     owner);
  }
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return ctx.FindAssocArray(InstanceMemberKey(base));
  return ResolveOn(obj, obj->type, base->rhs->text, ctx, owner);
}

void TypeForeachIterVar(std::string_view iter_name, const AssocArrayObject* aa,
                        SimContext& ctx) {
  if (aa == nullptr) return;
  if (!aa->index_class.empty())
    ctx.SetVariableClassType(iter_name, aa->index_class);
  if (!aa->index_type_name.empty() &&
      ctx.FindEnumType(aa->index_type_name) != nullptr)
    ctx.SetVariableEnumType(iter_name, aa->index_type_name);
}

}  // namespace delta
