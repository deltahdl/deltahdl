#include "elaborator/interface_property_instance.h"

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

const ModuleDecl* FindInterface(std::string_view name,
                                const CompilationUnit* unit) {
  for (const ModuleDecl* ifc : unit->interfaces) {
    if (ifc->name == name) return ifc;
  }
  return nullptr;
}

// The names `e` reads without a hierarchical path: every identifier but the
// member a `.` or `::` selects.
void CollectFreeNames(const Expr* e,
                      std::unordered_set<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.insert(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectFreeNames(e->lhs, out);
    return;
  }
  const Expr* children[] = {
      e->lhs,       e->rhs,       e->base,       e->index,        e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count, e->with_expr};
  for (const Expr* c : children) CollectFreeNames(c, out);
  for (const Expr* a : e->args) CollectFreeNames(a, out);
  for (const Expr* el : e->elements) CollectFreeNames(el, out);
}

Expr* InstanceMember(std::string_view inst, std::string_view name,
                     SourceLoc loc, Arena& arena) {
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = inst;
  base->range.start = loc;
  auto* member = arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = name;
  member->range.start = loc;
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = base;
  access->rhs = member;
  access->range.start = loc;
  return access;
}

// Each expression slot of a list of clocking events, the signal and the iff
// condition of each.
template <typename Fn>
void ForEachEventSlot(std::vector<EventExpr>& events, const Fn& fn) {
  for (EventExpr& ev : events) {
    fn(ev.signal);
    fn(ev.iff_condition);
  }
}

// Each expression slot of the match items of one operand.
template <typename Fn>
void ForEachItemSlot(std::vector<SeqMatchAssign>& items, const Fn& fn) {
  for (SeqMatchAssign& item : items) {
    fn(item.rhs);
    fn(item.call);
  }
}

// Each expression slot of a sequence body, those of its intersects,
// conjuncts and alternatives included, for a substitution to replace.
template <typename Fn>
void ForEachBodySlot(SeqLinearBody& body, const Fn& fn) {
  for (Expr*& operand : body.operands) fn(operand);
  for (auto& items : body.match_items) ForEachItemSlot(items, fn);
  ForEachItemSlot(body.first_match_items, fn);
  for (SeqLocalDecl& local : body.locals) fn(local.init);
  for (SeqThroughout& guard : body.throughouts) fn(guard.cond);
  for (auto& clock : body.clocks) ForEachEventSlot(clock, fn);
  ForEachEventSlot(body.clock_out, fn);
  for (SeqLinearBody& inner : body.intersects) ForEachBodySlot(inner, fn);
  for (SeqLinearBody& inner : body.conjuncts) ForEachBodySlot(inner, fn);
  for (SeqLinearBody& inner : body.alternatives) ForEachBodySlot(inner, fn);
}

// The names a sequence body declares as its local variables, which are no
// members of the interface.
void CollectBodyLocals(const SeqLinearBody& body,
                       std::unordered_set<std::string_view>& out) {
  for (const SeqLocalDecl& local : body.locals) out.insert(local.name);
  for (const SeqLinearBody& inner : body.intersects) {
    CollectBodyLocals(inner, out);
  }
  for (const SeqLinearBody& inner : body.conjuncts) {
    CollectBodyLocals(inner, out);
  }
  for (const SeqLinearBody& inner : body.alternatives) {
    CollectBodyLocals(inner, out);
  }
}

// A copy of the property tree under `node` whose nodes and sequences are the
// copy's own, so that its expressions can be replaced.
PropertyExprNode* CopyTree(const PropertyExprNode* node, Arena& arena) {
  auto* copy = arena.Create<PropertyExprNode>(*node);
  if (node->sequence != nullptr) {
    copy->sequence = arena.Create<ModuleItem>(*node->sequence);
  }
  for (PropertyExprNode*& operand : copy->operands) {
    operand = CopyTree(operand, arena);
  }
  return copy;
}

// Each expression slot of the tree under `node`, its sequences' included.
template <typename Fn>
void ForEachTreeSlot(PropertyExprNode* node, const Fn& fn) {
  fn(node->boolean);
  fn(node->range_min);
  fn(node->range_max);
  for (auto& values : node->case_values) {
    for (Expr*& value : values) fn(value);
  }
  ForEachEventSlot(node->clock, fn);
  if (node->sequence != nullptr) {
    ForEachBodySlot(node->sequence->seq_linear, fn);
    ForEachEventSlot(node->sequence->seq_clock, fn);
  }
  for (PropertyExprNode* operand : node->operands) {
    ForEachTreeSlot(operand, fn);
  }
}

// The locals the sequences of the tree under `node` declare.
void CollectTreeLocals(const PropertyExprNode* node,
                       std::unordered_set<std::string_view>& out) {
  if (node->sequence != nullptr) {
    CollectBodyLocals(node->sequence->seq_linear, out);
  }
  for (const PropertyExprNode* operand : node->operands) {
    CollectTreeLocals(operand, out);
  }
}

// §16.12 with §23.6: the tree of `decl`'s body as instance `inst` of its
// interface sees it, each name it reads that is neither a formal nor a
// local made the member of `inst` that the path reaches.
PropertyExprNode* InstanceTree(const ModuleItem* decl, std::string_view inst,
                               Arena& arena) {
  PropertyExprNode* tree = CopyTree(decl->prop_body_tree, arena);
  std::unordered_set<std::string_view> names;
  ForEachTreeSlot(tree, [&names](Expr*& e) { CollectFreeNames(e, names); });
  std::unordered_set<std::string_view> locals;
  CollectTreeLocals(tree, locals);
  for (const SeqLocalDecl& local : decl->prop_locals) locals.insert(local.name);
  for (std::string_view local : locals) names.erase(local);
  for (std::string_view formal : decl->prop_formals) names.erase(formal);
  ActualsByFormal members;
  for (std::string_view name : names) {
    members[name] = InstanceMember(inst, name, decl->loc, arena);
  }
  ForEachTreeSlot(tree, [&members, &arena](Expr*& e) {
    e = SubstituteFormals(e, members, arena);
  });
  return tree;
}

// `decl` as instance `inst` of its interface sees it: named "inst.name",
// with each name its body reads, a formal aside, made the member of `inst`
// that §23.6 reaches by the path.
ModuleItem* InstanceCopy(const ModuleItem* decl, std::string_view inst,
                         Arena& arena) {
  std::unordered_set<std::string_view> names;
  CollectFreeNames(decl->prop_body_expr, names);
  CollectFreeNames(decl->prop_disable_iff, names);
  for (const EventExpr& ev : decl->prop_clock) {
    CollectFreeNames(ev.signal, names);
    CollectFreeNames(ev.iff_condition, names);
  }
  for (std::string_view formal : decl->prop_formals) names.erase(formal);
  ActualsByFormal members;
  for (std::string_view name : names) {
    members[name] = InstanceMember(inst, name, decl->loc, arena);
  }
  auto* copy = arena.Create<ModuleItem>(*decl);
  copy->name = *arena.Create<std::string>(std::string(inst) + "." +
                                          std::string(decl->name));
  copy->prop_body_expr =
      SubstituteFormals(decl->prop_body_expr, members, arena);
  copy->prop_disable_iff =
      SubstituteFormals(decl->prop_disable_iff, members, arena);
  // A body the parser reads as the clocked boolean form is evaluated as the
  // boolean alone; one it reads as a tree alone, a temporal one, is the tree
  // with the instance's names in it.
  copy->prop_body_tree = decl->prop_body_expr != nullptr
                             ? nullptr
                             : InstanceTree(decl, inst, arena);
  for (EventExpr& ev : copy->prop_clock) {
    ev.signal = SubstituteFormals(ev.signal, members, arena);
    ev.iff_condition = SubstituteFormals(ev.iff_condition, members, arena);
  }
  return copy;
}

// The properties of the interface `ifc` as its instance `inst` sees them, each
// registered, and each whose body is a tree also appended to `run_decls`.
void RegisterInstanceCopies(const ModuleDecl* ifc, std::string_view inst,
                            PropertyRegistry& registry, Arena& arena,
                            std::vector<ModuleItem*>& run_decls) {
  for (const ModuleItem* member : ifc->items) {
    if (member->kind != ModuleItemKind::kPropertyDecl ||
        (member->prop_body_expr == nullptr &&
         member->prop_body_tree == nullptr)) {
      continue;
    }
    ModuleItem* copy = InstanceCopy(member, inst, arena);
    registry.Register(copy);
    if (copy->prop_body_tree != nullptr) run_decls.push_back(copy);
  }
}

}  // namespace

void RegisterInterfaceInstanceProperties(const ModuleDecl* decl,
                                         const CompilationUnit* unit,
                                         PropertyRegistry& registry,
                                         Arena& arena,
                                         std::vector<ModuleItem*>& run_decls) {
  if (decl == nullptr || unit == nullptr) return;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    const ModuleDecl* ifc = FindInterface(item->inst_module, unit);
    if (ifc == nullptr) continue;
    RegisterInstanceCopies(ifc, item->inst_name, registry, arena, run_decls);
  }
}

}  // namespace delta
