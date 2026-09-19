#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// Whether the class `type`, or one it inherits from, declares a property
// `name`.
bool DeclaresProperty(const ClassTypeInfo* type, std::string_view name) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    for (const auto& p : lvl->properties) {
      if (p.name == name) return true;
    }
  }
  return false;
}

// The bare identifiers `e` names, the field of a member access left out,
// which is resolved against what its base names.
void CollectIdentifiers(const Expr* e, std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectIdentifiers(e->lhs, out);
    return;
  }
  for (const Expr* sub : {e->lhs, e->rhs, e->base, e->index, e->index_end,
                          e->condition, e->true_expr, e->false_expr}) {
    CollectIdentifiers(sub, out);
  }
  for (const Expr* sub : e->args) CollectIdentifiers(sub, out);
  for (const Expr* sub : e->elements) CollectIdentifiers(sub, out);
}

// The identifiers the relations of the inline block `m` name: its hard and
// soft relations and the targets and items of its distributions.
std::vector<std::string_view> InlineIdentifiers(const ClassMember* m) {
  std::vector<std::string_view> names;
  for (const Expr* rel : m->constraint_exprs) CollectIdentifiers(rel, names);
  for (const Expr* rel : m->constraint_soft_exprs)
    CollectIdentifiers(rel, names);
  for (const auto& ref : m->constraint_dist_refs) {
    CollectIdentifiers(ref.target, names);
    for (const auto& item : ref.items) {
      CollectIdentifiers(item.value, names);
      CollectIdentifiers(item.lo, names);
      CollectIdentifiers(item.hi, names);
      CollectIdentifiers(item.weight, names);
    }
  }
  return names;
}

}  // namespace

// 18.7: a name of an unrestricted inline block that does not resolve in the
// class of the object being randomized is resolved starting in the scope
// containing the call, and a name of a restricted block not among the
// listed ones is resolved there whether or not the object declares it. The
// block is evaluated with the object in scope as `this`, so a member of the
// object whose method contains the call, the clause's y of C2 in the block
// of doit, is out of its reach there: each such member the block names,
// that no local of the call answers, is bound here as a local holding the
// member's value, in the scope the caller pushed for the call.
void BindCallersMembers(const Expr* expr, ClassObject* obj, SimContext& ctx,
                        Arena& arena) {
  const ClassMember* block = expr->inline_constraint;
  ClassObject* caller = ctx.CurrentThis();
  if (block == nullptr || caller == nullptr || caller == obj ||
      caller->type == nullptr || obj->type == nullptr) {
    return;
  }
  std::unordered_set<std::string_view> listed(expr->with_restrict_ids.begin(),
                                              expr->with_restrict_ids.end());
  std::unordered_set<std::string_view> bound;
  for (std::string_view name : InlineIdentifiers(block)) {
    bool objects = expr->with_has_parens ? listed.count(name) != 0
                                         : DeclaresProperty(obj->type, name);
    if (objects || !DeclaresProperty(caller->type, name) ||
        ctx.FindLocalVariable(name) != nullptr || !bound.insert(name).second) {
      continue;
    }
    Logic4Vec value = caller->GetProperty(name, arena);
    Variable* local =
        ctx.CreateLocalVariable(name, value.width, value.is_signed);
    local->value = value;
  }
}

// 18.7: a name of a restricted block that is not listed resolves in the scope
// containing the call whether or not the object declares it. The block is
// evaluated with the object as `this`, and a bare name a method's class
// declares resolves to the property before the enclosing scope's variable
// (NameDenotesVariable, §23.9), so such a name would read the object's own
// member: each unlisted name the object declares that a variable of the
// calling scope answers, and no local of the call shadows, is bound here as a
// local holding that variable's value, in the scope the caller pushed.
void BindCallersVariables(const Expr* expr, ClassObject* obj, SimContext& ctx,
                          Arena& arena) {
  const ClassMember* block = expr->inline_constraint;
  if (block == nullptr || !expr->with_has_parens || obj->type == nullptr) {
    return;
  }
  std::unordered_set<std::string_view> listed(expr->with_restrict_ids.begin(),
                                              expr->with_restrict_ids.end());
  std::unordered_set<std::string_view> bound;
  for (std::string_view name : InlineIdentifiers(block)) {
    if (listed.count(name) != 0 || !DeclaresProperty(obj->type, name) ||
        ctx.FindLocalVariable(name) != nullptr || !bound.insert(name).second) {
      continue;
    }
    const Variable* var = ctx.FindVariable(name);
    if (var == nullptr) continue;
    Variable* local =
        ctx.CreateLocalVariable(name, var->value.width, var->is_signed);
    local->value = OwnRhsWords(var->value, arena);
  }
}

}  // namespace delta
