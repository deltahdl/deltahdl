#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_class.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// §37.34: the constraint object a constraint block stands as, which a class
// defn, a class obj and a call of randomize written with an inline constraint
// block each hold, with the constraint expressions of its block (§37.38).

namespace delta {

namespace {

// What a constraint block's items are built with: the names their expressions
// resolve in, `scope` and the scopes around it first, the run a constant's
// value is evaluated in, and the build.
struct ItemBuild {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen;
  VpiObject* scope;
  SimContext& ctx;
  const VpiAttachBuild& build;

  VpiObject* Expression(const Expr* expr) const {
    return VpiGenBlockExpression(expr, {objects, prefix, gen, scope}, ctx,
                                 build);
  }
};

void Append(std::vector<VpiObject*>& list, VpiObject* obj) {
  if (obj != nullptr) list.push_back(obj);
}

std::vector<VpiObject*> MakeItems(const std::vector<ConstraintItem*>& items,
                                  const ItemBuild& at);

// §37.38: an implication, a constr if or a constr if else, reaching its guard
// through vpiCondition and the constraint expressions it governs through
// vpiConstraintExpr, those of an else branch through vpiElseConst.
VpiObject* GuardedItem(int type, const ConstraintItem& item,
                       const ItemBuild& at) {
  VpiObject* guarded = at.build.alloc();
  guarded->type = type;
  Append(guarded->children, at.Expression(item.expr));
  guarded->constraint_exprs = MakeItems(item.body, at);
  guarded->else_constraint_exprs = MakeItems(item.else_body, at);
  return guarded;
}

// §37.38 details 1 and 2: a constr foreach, reaching the array it indexes
// through vpiVariables and an int var per index variable it names through
// vpiLoopVars, a skipped one standing as none. The names of its body find the
// index variables first, and then what the foreach's own names find.
VpiObject* ForeachItem(const ConstraintItem& item, const ItemBuild& at) {
  VpiObject* loop = at.build.alloc();
  loop->type = vpiConstrForEach;
  loop->parent = at.scope;
  loop->foreach_array = at.Expression(item.expr);
  for (std::string_view name : item.loop_vars) {
    VpiObject* index = nullptr;
    if (!name.empty()) {
      index = at.build.alloc();
      index->type = vpiIntVar;
      index->name = at.build.keep(std::string(name));
      index->parent = loop;
    }
    loop->loop_vars.push_back(index);
  }
  const ItemBuild kBody{at.objects, at.prefix, at.gen, loop, at.ctx, at.build};
  loop->constraint_exprs = MakeItems(item.body, kBody);
  return loop;
}

// §37.38: a soft disable, reaching the expression whose soft constraints it
// discards (§18.5.13.2).
VpiObject* SoftDisableItem(const ConstraintItem& item, const ItemBuild& at) {
  VpiObject* disable = at.build.alloc();
  disable->type = vpiSoftDisable;
  Append(disable->children, at.Expression(item.expr));
  return disable;
}

// §37.34: a dist item of the distribution `dist`, reaching its value, or the
// range [lo:hi] it gives, through vpiValueRange and its weight through
// vpiWeight, and reporting through vpiDistType whether the weight is given
// each value of a range, :=, or the item as a whole, :/ (§18.5.3). A default
// item and a range written about a centre (§11.4.13) reach no value range,
// and an item written with no weight reaches none either.
VpiObject* DistItem(const ConstraintDistItem& entry, VpiObject* dist,
                    const ItemBuild& at) {
  VpiObject* item = at.build.alloc();
  item->type = vpiDistItem;
  item->parent = dist;
  item->dist_type = entry.per_element ? vpiEqualDist : vpiDivDist;
  item->weight = at.Expression(entry.weight);
  if (!entry.is_range) {
    item->value_range = at.Expression(entry.value);
  } else if (entry.hi != nullptr) {
    VpiObject* range = at.build.alloc();
    range->type = vpiRange;
    range->parent = item;
    range->left_range = at.Expression(entry.lo);
    range->right_range = at.Expression(entry.hi);
    item->value_range = range;
  }
  return item;
}

// §37.34 and §37.38: a distribution, reaching the expression it weights and a
// dist item per entry of its list, in order.
VpiObject* DistributionItem(const ConstraintItem& item, const ItemBuild& at) {
  VpiObject* dist = at.build.alloc();
  dist->type = vpiDistribution;
  Append(dist->children, at.Expression(item.expr));
  for (const ConstraintDistItem& entry : item.dist) {
    dist->children.push_back(DistItem(entry, dist, at));
  }
  return dist;
}

// §37.34: a constraint ordering, reaching the expressions it solves before
// through vpiSolveBefore and those it solves after through vpiSolveAfter
// (§18.5.9).
VpiObject* OrderingItem(const ConstraintItem& item, const ItemBuild& at) {
  VpiObject* ordering = at.build.alloc();
  ordering->type = vpiConstraintOrdering;
  for (const Expr* expr : item.exprs) {
    Append(ordering->solve_before, at.Expression(expr));
  }
  for (const Expr* expr : item.after) {
    Append(ordering->solve_after, at.Expression(expr));
  }
  return ordering;
}

// §37.34 and §37.38: the constraint item `item` writes, a constraint ordering
// or a constraint expression; null for one §37.38 draws no object for, a
// uniqueness constraint (§18.5.4).
VpiObject* MakeItem(const ConstraintItem& item, const ItemBuild& at) {
  switch (item.kind) {
    case ConstraintItemKind::kExpression:
      return item.has_dist ? DistributionItem(item, at)
                           : at.Expression(item.expr);
    case ConstraintItemKind::kImplication:
      return GuardedItem(vpiImplication, item, at);
    case ConstraintItemKind::kIfElse:
      return GuardedItem(item.has_else ? vpiConstrIfElse : vpiConstrIf, item,
                         at);
    case ConstraintItemKind::kForeach:
      return ForeachItem(item, at);
    case ConstraintItemKind::kDisableSoft:
      return SoftDisableItem(item, at);
    case ConstraintItemKind::kSolveBefore:
      return OrderingItem(item, at);
    default:
      return nullptr;
  }
}

std::vector<VpiObject*> MakeItems(const std::vector<ConstraintItem*>& items,
                                  const ItemBuild& at) {
  std::vector<VpiObject*> made;
  for (const ConstraintItem* item : items) {
    VpiObject* obj = MakeItem(*item, at);
    if (obj == nullptr) continue;
    // §18.5.13: an expression written soft reports so through vpiSoft. A name
    // standing alone is the variable it names, no object of the item's own.
    if (item->soft && VpiIsExprType(obj->type)) obj->soft = true;
    made.push_back(obj);
  }
  return made;
}

}  // namespace

VpiObject* VpiBaseClassDefn(const VpiObject* defn) {
  for (const VpiObject* child : defn->children) {
    if (child->type != vpiExtends) continue;
    for (VpiObject* typespec : child->children) {
      if (typespec->type == vpiClassTypespec && !typespec->children.empty()) {
        return typespec->children.front();
      }
    }
  }
  return nullptr;
}

VpiObject* VpiClassNameScope(const VpiObject* defn, VpiObject* outer,
                             const VpiAttachBuild& build) {
  VpiObject* scope = build.alloc();
  scope->parent = outer;
  for (const VpiObject* at = defn; at != nullptr; at = VpiBaseClassDefn(at)) {
    for (VpiObject* child : at->children) {
      if (VpiIsVariablesType(child->type)) scope->children.push_back(child);
    }
  }
  return scope;
}

VpiObject* VpiMakeConstraint(const ClassMember& block, VpiObject* holder,
                             const VpiConstraintNames& names,
                             const VpiAttachBuild& build) {
  VpiObject* constraint = build.alloc();
  constraint->type = vpiConstraint;
  constraint->name = build.keep(std::string(block.name));
  if (holder->type == vpiClassDefn) {
    constraint->full_name = holder->full_name + "::" + std::string(block.name);
  }
  constraint->parent = holder;
  constraint->automatic = !block.is_static;
  constraint->access_type = block.is_constraint_prototype ? vpiExternAcc : 0;
  constraint->constraint_enabled = true;
  constraint->children = MakeItems(
      block.constraint_items,
      {names.objects, names.prefix, names.gen, names.scope, names.ctx, build});
  return constraint;
}

}  // namespace delta
