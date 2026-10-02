#include <format>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

// §19.3: a covergroup is a user-defined type whose instances `new` builds,
// and a variable of it holds a handle to one. This is where a `new` finds the
// variable, element, property or embedded covergroup it builds for, and where
// the handle is stored.

namespace delta {

namespace {

// §19.3: the covergroup type of the property `name` of the class `type`
// declares or inherits; null where it declares none of the name, or one of no
// covergroup type.
const CovergroupDecl* PropertyCovergroup(const ClassTypeInfo* type,
                                         std::string_view name,
                                         SimContext& ctx) {
  for (; type != nullptr && type->decl != nullptr; type = type->parent) {
    for (const ClassMember* member : type->decl->members) {
      if (member->kind == ClassMemberKind::kProperty && member->name == name) {
        return CovergroupOfType(member->data_type, ctx);
      }
    }
  }
  return nullptr;
}

// The class whose properties `lhs`, an identifier or a member access, names
// one of: the running object's for a bare name, the object's `h` holds for
// `h.p`, and K for `K::s`; null for none. `owner` is set to the object where
// there is one.
const ClassTypeInfo* ClassOfTarget(const Expr* lhs, SimContext& ctx,
                                   Arena& arena, ClassObject*& owner) {
  if (lhs->kind == ExprKind::kIdentifier) {
    owner = ctx.CurrentThis();
  } else if (lhs->is_scope_resolution) {
    return ctx.FindClassType(lhs->lhs->text);
  } else {
    owner = ObjectNamed(lhs->lhs, ctx, arena);
  }
  return owner != nullptr ? owner->type : nullptr;
}

// §19.3 and §19.4: where an assignment of `new` to `lhs` builds its
// instance: a covergroup the class of the running object, or of `h` in
// `h.cg`, embeds; a property or static property of a covergroup type; or a
// variable of one, an element of an array of them among them. A site of no
// covergroup where `lhs` is of no covergroup type.
CovergroupSite NewSiteOf(const Expr* lhs, SimContext& ctx, Arena& arena) {
  if (lhs->kind != ExprKind::kIdentifier &&
      lhs->kind != ExprKind::kMemberAccess) {
    const CovergroupDecl* decl =
        ctx.Covergroups().DeclaredOf(ResolveLhsVariable(lhs, ctx));
    if (decl == nullptr) return {};
    return {HierarchicalReferenceName(lhs->base), decl, nullptr};
  }
  ClassObject* owner = nullptr;
  const ClassTypeInfo* cls = ClassOfTarget(lhs, ctx, arena, owner);
  std::string_view name =
      lhs->kind == ExprKind::kIdentifier ? lhs->text : lhs->rhs->text;
  if (owner != nullptr) {
    if (const CovergroupDecl* decl =
            ctx.Covergroups().Embedded(owner->type, name)) {
      return {CovergroupTable::EmbeddedKey(owner, name), decl, owner};
    }
  }
  if (cls != nullptr) {
    if (const CovergroupDecl* decl = PropertyCovergroup(cls, name, ctx)) {
      return {std::string(name), decl, nullptr};
    }
    if (lhs->kind != ExprKind::kIdentifier) return {};
  }
  const CovergroupDecl* decl =
      ctx.Covergroups().DeclaredOf(ResolveLhsVariable(lhs, ctx));
  if (decl == nullptr) return {};
  return {HierarchicalReferenceName(lhs), decl, nullptr};
}

// §19.3: the handle of `inst`, the value a variable holding it stores.
Logic4Vec HandleOf(const CovergroupInstance* inst, SimContext& ctx,
                   Arena& arena) {
  return MakeLogic4VecVal(arena, 64, ctx.Covergroups().IdentityOf(inst));
}

// Whether `e` is a call of `new`, which builds an instance.
bool IsNewCall(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kCall && e->text == "new";
}

// §19.3: builds at `site` the instance an initializer `new(...)`, `init`,
// makes, and stores its handle in `v`; nothing for any other initializer.
void HoldNewInstance(Variable* v, const CovergroupSite& site, const Expr* init,
                     SimContext& ctx, Arena& arena) {
  if (!IsNewCall(init)) return;
  v->value =
      HandleOf(BuildCovergroupInstance(site, init, ctx, arena), ctx, arena);
}

}  // namespace

void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena) {
  ctx.Covergroups().Declare(v, var.covergroup);
  HoldNewInstance(
      v, {std::string(name), var.covergroup, nullptr, &var.gen_block_consts},
      var.init_expr, ctx, arena);
}

const CovergroupDecl* CovergroupOfType(const DataType& type, SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return nullptr;
  std::string key =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::format("{}::{}", type.scope_name, type.type_name);
  const ModuleItem* item = ctx.FindLetDecl(key);
  if (item == nullptr || item->kind != ModuleItemKind::kCovergroupDecl) {
    return nullptr;
  }
  return item->covergroup;
}

bool TryCreateCovergroupLocal(const DataType& type, const Expr* init,
                              Variable* v, SimContext& ctx, Arena& arena) {
  const CovergroupDecl* decl = CovergroupOfType(type, ctx);
  if (decl == nullptr) return false;
  ctx.Covergroups().Declare(v, decl);
  v->value = MakeLogic4VecVal(arena, 64, 0);
  HoldNewInstance(v, {std::string(decl->name), decl, nullptr}, init, ctx,
                  arena);
  return true;
}

std::optional<Logic4Vec> CovergroupPropertyNew(const ClassTypeInfo* type,
                                               std::string_view name,
                                               const Expr* init,
                                               SimContext& ctx, Arena& arena) {
  const CovergroupDecl* decl = PropertyCovergroup(type, name, ctx);
  if (decl == nullptr) return std::nullopt;
  return HandleOf(BuildCovergroupInstance({std::string(name), decl, nullptr},
                                          init, ctx, arena),
                  ctx, arena);
}

bool TryCovergroupNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const Expr* rhs = stmt->rhs;
  if (stmt->lhs == nullptr || !IsNewCall(rhs)) return false;
  CovergroupSite site = NewSiteOf(stmt->lhs, ctx, arena);
  if (site.decl == nullptr) return false;
  CovergroupInstance* inst = BuildCovergroupInstance(site, rhs, ctx, arena);
  if (site.owner == nullptr) {
    PerformBlockingAssign(stmt->lhs, HandleOf(inst, ctx, arena), ctx, arena);
  }
  return true;
}

}  // namespace delta
