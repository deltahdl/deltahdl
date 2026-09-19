#include "simulator/eval_array_class_assoc.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

// §8.5/§7.8: the declaration of the property `name` on the class chain from
// `type` whose one unpacked dimension is an index type, and the class that
// declares it in `declaring`. The nearest declaration is the one that answers
// (§8.13): a class between that redeclares the name as something else hides
// the associative one below it, and answers null.
const ClassMember* FindAssocPropertyDecl(const ClassTypeInfo* type,
                                         std::string_view name, SimContext& ctx,
                                         const ClassTypeInfo*& declaring) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* member : t->decl->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name)
        continue;
      if (member->is_param || member->unpacked_dims.size() != 1 ||
          !IsAssocIndexDim(member->unpacked_dims[0], ctx)) {
        return nullptr;
      }
      declaring = t;
      return member;
    }
  }
  return nullptr;
}

// §7.8: the array the declaration `member` of class `declaring` asks for,
// empty. The element takes the width and state-ness the class's property
// record gives it, which is what a scalar property of the same declaration is
// written with; the index takes the type the dimension names.
AssocArrayObject* MakeAssocProperty(const ClassTypeInfo* declaring,
                                    const ClassMember* member,
                                    SimContext& ctx) {
  const auto* prop = declaring->FindProperty(member->name);
  uint32_t elem_width = prop != nullptr ? prop->width : 32;
  bool elem_4state = prop != nullptr && prop->is_4state;
  const Expr* dim = member->unpacked_dims[0];
  AssocArraySpec spec = AssocIndexSpec(dim, elem_4state, ctx);
  auto* aa = ctx.GetArena().Create<AssocArrayObject>();
  aa->elem_width = elem_width;
  aa->is_string_key = dim->text == "string";
  aa->is_wildcard = spec.is_wildcard;
  aa->index_width = spec.index_width;
  aa->is_4state = spec.is_4state;
  aa->is_index_signed = spec.is_index_signed;
  return aa;
}

// Whether `expr` is a path of names to an object -- an identifier, `this`
// among them, or a member access down such a path -- which is evaluated to a
// handle without running anything. A call or a select on the way is not, and
// is left to the paths that own it rather than evaluated here and again there.
bool IsHandlePath(const Expr* expr) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) return true;
  return expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution &&
         expr->rhs != nullptr && expr->rhs->kind == ExprKind::kIdentifier &&
         IsHandlePath(expr->lhs);
}

// The object a member access's handle side names: the running method's object
// for `this` (§8.11), else the object the handle the side evaluates to refers
// to; null for a side that is no handle path or a null handle.
ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena) {
  if (!IsHandlePath(side)) return nullptr;
  if (side->kind == ExprKind::kIdentifier && side->text == "this")
    return ctx.CurrentThis();
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

// The array ClassAssocProperty answers, with `owner` set to the object whose
// property it is, or to null for a static property's, which no object owns.
AssocArrayObject* ResolveOn(ClassObject* obj, const ClassTypeInfo* from,
                            std::string_view name, SimContext& ctx,
                            ClassObject** owner) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = FindAssocPropertyDecl(from, name, ctx, declaring);
  if (member == nullptr) return nullptr;
  if (member->is_static) {
    auto& slot = declaring->static_assoc_properties[std::string(name)];
    if (slot == nullptr) slot = MakeAssocProperty(declaring, member, ctx);
    return slot;
  }
  if (obj == nullptr) return nullptr;
  auto& slot = obj->assoc_properties[std::string(name)];
  if (slot == nullptr) slot = MakeAssocProperty(declaring, member, ctx);
  if (owner != nullptr) *owner = obj;
  return slot;
}

// §8.23: `C::name` names the static property `name` of class C.
AssocArrayObject* ScopeResolvedAssocProperty(const Expr* base,
                                             SimContext& ctx) {
  if (base->lhs == nullptr || base->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  const ClassTypeInfo* cls = ctx.FindClassType(base->lhs->text);
  if (cls == nullptr) return nullptr;
  return ResolveOn(nullptr, cls, base->rhs->text, ctx, nullptr);
}

}  // namespace

AssocArrayObject* ClassAssocProperty(ClassObject* obj,
                                     const ClassTypeInfo* from,
                                     std::string_view name, SimContext& ctx) {
  return ResolveOn(obj, from, name, ctx, nullptr);
}

AssocArrayObject* FindAssocArrayOfName(std::string_view name, SimContext& ctx,
                                       ClassObject** owner) {
  if (owner != nullptr) *owner = nullptr;
  if (auto* aa = ctx.FindAssocArray(name)) return aa;
  // Outside a method there is no class scope to resolve the name in, and this
  // is asked of every element select, so that is settled before the lookups.
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  if (from == nullptr && self != nullptr) from = self->type;
  if (from == nullptr) return nullptr;
  // A local of the same name is the name's own declaration and shadows the
  // property, so the property is asked for only where no local answers.
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
  if (base->kind != ExprKind::kMemberAccess || base->lhs == nullptr ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (base->is_scope_resolution) return ScopeResolvedAssocProperty(base, ctx);
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return nullptr;
  return ResolveOn(obj, obj->type, base->rhs->text, ctx, owner);
}

}  // namespace delta
