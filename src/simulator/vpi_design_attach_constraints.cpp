#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir_attribute.h"
#include "parser/ast_class.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct ItemBuild {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen;
  VpiObject* scope;
  SimContext& ctx;
  const VpiAttachBuild& build;
  const RtlirNodeAttributes* attrs = nullptr;
  const VpiCallStand* stand = nullptr;

  VpiObject* Expression(const Expr* expr) const {
    return VpiGenBlockExpression(
        expr, {objects, prefix, gen, scope, attrs, stand}, ctx, build);
  }
};

void Append(std::vector<VpiObject*>& list, VpiObject* obj) {
  if (obj != nullptr) list.push_back(obj);
}

std::vector<VpiObject*> MakeItems(const std::vector<ConstraintItem*>& items,
                                  const ItemBuild& at);

VpiObject* GuardedItem(int type, const ConstraintItem& item,
                       const ItemBuild& at) {
  VpiObject* guarded = at.build.alloc();
  guarded->type = type;
  Append(guarded->children, at.Expression(item.expr));
  guarded->constraint_exprs = MakeItems(item.body, at);
  guarded->else_constraint_exprs = MakeItems(item.else_body, at);
  return guarded;
}

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
  const ItemBuild kBody{at.objects, at.prefix, at.gen,   loop,
                        at.ctx,     at.build,  at.attrs, at.stand};
  loop->constraint_exprs = MakeItems(item.body, kBody);
  return loop;
}

VpiObject* SoftDisableItem(const ConstraintItem& item, const ItemBuild& at) {
  VpiObject* disable = at.build.alloc();
  disable->type = vpiSoftDisable;
  Append(disable->children, at.Expression(item.expr));
  return disable;
}

VpiObject* DistItem(const ConstraintDistItem& entry, VpiObject* dist,
                    const std::function<VpiObject*()>& alloc,
                    const std::function<VpiObject*(const Expr*)>& expression) {
  VpiObject* item = alloc();
  item->type = vpiDistItem;
  item->parent = dist;
  item->dist_type = entry.per_element ? vpiEqualDist : vpiDivDist;
  item->weight = expression(entry.weight);
  if (!entry.is_range) {
    item->value_range = expression(entry.value);
  } else if (entry.hi != nullptr) {
    VpiObject* range = alloc();
    range->type = vpiRange;
    range->parent = item;
    range->left_range = expression(entry.lo);
    range->right_range = expression(entry.hi);
    item->value_range = range;
  }
  return item;
}

VpiObject* DistributionItem(const ConstraintItem& item, const ItemBuild& at) {
  return VpiMakeDistribution(
      at.Expression(item.expr), item.dist, at.build.alloc,
      [&at](const Expr* expr) { return at.Expression(expr); });
}

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

VpiObject* VpiMakeDistribution(
    VpiObject* weighted, const std::vector<ConstraintDistItem>& items,
    const std::function<VpiObject*()>& alloc,
    const std::function<VpiObject*(const Expr*)>& expression) {
  VpiObject* dist = alloc();
  dist->type = vpiDistribution;
  Append(dist->children, weighted);
  for (const ConstraintDistItem& entry : items) {
    dist->children.push_back(DistItem(entry, dist, alloc, expression));
  }
  return dist;
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
  constraint->is_virtual = block.is_pure_virtual;
  constraint->access_type =
      block.is_constraint_prototype && !block.is_pure_virtual ? vpiExternAcc
                                                              : 0;
  constraint->constraint_enabled = true;
  constraint->children =
      MakeItems(block.constraint_items,
                {names.objects, names.prefix, names.gen, names.scope, names.ctx,
                 build, names.attrs, names.stand});
  return constraint;
}

}  // namespace delta
