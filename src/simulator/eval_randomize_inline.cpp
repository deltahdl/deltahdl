#include <functional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
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

// Each expression the distributions `refs` hold: their targets, values,
// bounds, tolerances and weights.
void ForEachDistExpr(const std::vector<ConstraintDistRef>& refs,
                     const std::function<void(const Expr*)>& fn) {
  for (const auto& ref : refs) {
    fn(ref.target);
    for (const auto& item : ref.items) {
      for (const Expr* e :
           {item.value, item.lo, item.hi, item.tolerance, item.weight})
        fn(e);
    }
  }
}

// Each expression the inline block `m` holds: its hard and soft relations
// and distributions, the relations of its foreach constraints and the
// members of its uniqueness constraints.
void ForEachInlineExpr(const ClassMember* m,
                       const std::function<void(const Expr*)>& fn) {
  for (const Expr* rel : m->constraint_exprs) fn(rel);
  for (const Expr* rel : m->constraint_soft_exprs) fn(rel);
  ForEachDistExpr(m->constraint_dist_refs, fn);
  ForEachDistExpr(m->constraint_soft_dist_refs, fn);
  for (const auto& ref : m->constraint_foreach_refs) {
    for (const Expr* rel : ref.body) fn(rel);
  }
  for (const auto& group : m->constraint_unique_refs) {
    for (const Expr* member : group) fn(member);
  }
}

// The identifiers the expressions of the inline block `m` name.
std::vector<std::string_view> InlineIdentifiers(const ClassMember* m) {
  std::vector<std::string_view> names;
  ForEachInlineExpr(m,
                    [&names](const Expr* e) { CollectIdentifiers(e, names); });
  return names;
}

constexpr std::string_view kLocalPrefix = "local.";

// Whether `e` is a name qualified by local::, `local::x` or
// `local::super.lim`, read by the path it spells.
bool IsLocalQualifiedName(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess &&
         HierarchicalReferenceName(e).starts_with(kLocalPrefix);
}

// The local::-qualified names `e` reads as values: not the callee of a
// call, nor the type of a cast, nor an array a select indexes, which are
// resolved where they are used.
void CollectLocalNames(const Expr* e, std::vector<const Expr*>& out) {
  if (e == nullptr) return;
  if (IsLocalQualifiedName(e)) {
    out.push_back(e);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess || e->kind == ExprKind::kCast) {
    CollectLocalNames(e->lhs, out);
    return;
  }
  if (e->kind != ExprKind::kCall) {
    for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                            e->false_expr, e->index, e->index_end}) {
      CollectLocalNames(sub, out);
    }
    if (e->base != nullptr && !IsLocalQualifiedName(e->base))
      CollectLocalNames(e->base, out);
  }
  for (const Expr* sub : e->args) CollectLocalNames(sub, out);
  for (const Expr* sub : e->elements) CollectLocalNames(sub, out);
}

// The head identifier of each dotted name `e` holds, `h` of `h.v`.
void CollectDottedHeads(const Expr* e, std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kMemberAccess) {
    const Expr* head = e->lhs;
    while (head->kind == ExprKind::kMemberAccess) head = head->lhs;
    if (!e->is_scope_resolution && head->kind == ExprKind::kIdentifier)
      out.push_back(head->text);
    return;
  }
  for (const Expr* sub : {e->lhs, e->rhs, e->base, e->index, e->index_end,
                          e->condition, e->true_expr, e->false_expr}) {
    CollectDottedHeads(sub, out);
  }
  for (const Expr* sub : e->args) CollectDottedHeads(sub, out);
  for (const Expr* sub : e->elements) CollectDottedHeads(sub, out);
}

// The value of the local::-qualified name `e`, spelled `path`, read in the
// scope containing the call: a property of the object of the method making
// the call where no variable answers its bare name, and otherwise the name
// as that scope resolves it, `super` and `this` naming the method's own.
Logic4Vec LocalQualifiedValue(const Expr* e, const std::string& path,
                              SimContext& ctx, Arena& arena) {
  std::string_view name = std::string_view(path).substr(kLocalPrefix.size());
  ClassObject* self = ctx.CurrentThis();
  if (self != nullptr && name.find('.') == std::string_view::npos &&
      ctx.FindVariable(name) == nullptr) {
    return self->GetProperty(name, arena);
  }
  return EvalExpr(e, ctx, arena);
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

// 18.7.1: a name qualified by local:: resolves in the scope containing the
// call, which is the scope this runs in: before the object is bound as
// `this`, and before a trial binds the object's random variables as locals
// of their names. Each local::-qualified name the block reads is read here
// and bound, in the scope the caller pushed, as a local named by its
// qualified path, `local.x`, which the block's evaluation reads
// (TryLocalScopeQualifier).
void BindLocalQualifiedNames(const Expr* expr, SimContext& ctx, Arena& arena) {
  const ClassMember* block = expr->inline_constraint;
  if (block == nullptr) return;
  std::vector<const Expr*> names;
  ForEachInlineExpr(block,
                    [&names](const Expr* e) { CollectLocalNames(e, names); });
  for (const Expr* e : names) {
    std::string path = HierarchicalReferenceName(e);
    Logic4Vec value = LocalQualifiedValue(e, path, ctx, arena);
    std::string_view key(arena.AllocString(path.data(), path.size()),
                         path.size());
    Variable* local =
        ctx.CreateLocalVariable(key, value.width, value.is_signed);
    local->value = value;
  }
}

// 18.7: a dotted name of the block not qualified by this, super or local::
// resolves downwards starting in the class of the object being randomized
// (23.3), and only where it does not resolve there in the scope containing
// the call; a restricted block resolves so only a name its list holds. The
// head of such a name the object declares, which a variable visible from the
// call would otherwise answer, is bound here, in the scope the caller
// pushed, as a local holding the object's handle, with its class.
void BindObjectHandleHeads(const Expr* expr, ClassObject* obj, SimContext& ctx,
                           Arena& arena) {
  const ClassMember* block = expr->inline_constraint;
  if (block == nullptr) return;
  std::unordered_set<std::string_view> listed(expr->with_restrict_ids.begin(),
                                              expr->with_restrict_ids.end());
  std::vector<std::string_view> heads;
  ForEachInlineExpr(block,
                    [&heads](const Expr* e) { CollectDottedHeads(e, heads); });
  std::unordered_set<std::string_view> bound;
  for (std::string_view head : heads) {
    if (!DeclaresProperty(obj->type, head) ||
        (expr->with_has_parens && listed.count(head) == 0) ||
        ctx.FindVariable(head) == nullptr || !bound.insert(head).second) {
      continue;
    }
    Logic4Vec value = obj->GetProperty(head, arena);
    Variable* local =
        ctx.CreateLocalVariable(head, value.width, value.is_signed);
    local->value = value;
    if (const ClassObject* held = ctx.GetClassObject(value.ToUint64()))
      ctx.RecordLocalClassType(head, held->type->name);
  }
}

}  // namespace delta
