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

bool DeclaresProperty(const ClassTypeInfo* type, std::string_view name) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    for (const auto& p : lvl->properties) {
      if (p.name == name) return true;
    }
  }
  return false;
}

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

std::vector<std::string_view> InlineIdentifiers(const ClassMember* m) {
  std::vector<std::string_view> names;
  ForEachInlineExpr(m,
                    [&names](const Expr* e) { CollectIdentifiers(e, names); });
  return names;
}

constexpr std::string_view kLocalPrefix = "local.";

bool IsLocalQualifiedName(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess &&
         HierarchicalReferenceName(e).starts_with(kLocalPrefix);
}

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
