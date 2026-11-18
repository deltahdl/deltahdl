#include "elaborator/interface_property_instance.h"

#include <string>
#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/assertion_body_slots.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

const ModuleDecl* FindInterface(std::string_view name,
                                const CompilationUnit* unit) {
  for (const ModuleDecl* ifc : unit->interfaces) {
    if (ifc->name == name && !ifc->is_extern) return ifc;
  }
  return nullptr;
}

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
  const Expr* children[] = {e->lhs,       e->rhs,         e->base,
                            e->index,     e->index_end,   e->condition,
                            e->true_expr, e->false_expr,  e->repeat_count,
                            e->with_expr, e->stream_range};
  for (const Expr* c : children) CollectFreeNames(c, out);
  for (const Expr* a : e->args) CollectFreeNames(a, out);
  for (const Expr* el : e->elements) CollectFreeNames(el, out);
}

ActualsByFormal InstanceMembers(
    const std::unordered_set<std::string_view>& names, std::string_view inst,
    SourceLoc loc, Arena& arena) {
  ActualsByFormal members;
  for (std::string_view name : names) {
    members[name] = MemberOf(inst, name, loc, arena);
  }
  return members;
}

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
  ActualsByFormal members = InstanceMembers(names, inst, decl->loc, arena);
  ForEachTreeSlot(tree, [&members, &arena](Expr*& e) {
    e = SubstituteFormals(e, members, arena);
  });
  return tree;
}

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
  ActualsByFormal members = InstanceMembers(names, inst, decl->loc, arena);
  auto* copy = arena.Create<ModuleItem>(*decl);
  copy->name = *arena.Create<std::string>(std::string(inst) + "." +
                                          std::string(decl->name));
  copy->prop_body_expr =
      SubstituteFormals(decl->prop_body_expr, members, arena);
  copy->prop_disable_iff =
      SubstituteFormals(decl->prop_disable_iff, members, arena);
  copy->prop_body_tree = decl->prop_body_expr != nullptr
                             ? nullptr
                             : InstanceTree(decl, inst, arena);
  for (EventExpr& ev : copy->prop_clock) {
    ev.signal = SubstituteFormals(ev.signal, members, arena);
    ev.iff_condition = SubstituteFormals(ev.iff_condition, members, arena);
  }
  return copy;
}

ModuleItem* InstanceSequence(const ModuleItem* decl, std::string_view inst,
                             Arena& arena) {
  auto* copy = arena.Create<ModuleItem>(*decl);
  copy->name = *arena.Create<std::string>(std::string(inst) + "." +
                                          std::string(decl->name));
  std::unordered_set<std::string_view> names;
  auto collect = [&names](Expr*& e) { CollectFreeNames(e, names); };
  ForEachBodySlot(copy->seq_linear, collect);
  ForEachEventSlot(copy->seq_clock, collect);
  std::unordered_set<std::string_view> locals;
  CollectBodyLocals(copy->seq_linear, locals);
  for (std::string_view local : decl->prop_seq_assert_vars) {
    locals.insert(local);
  }
  for (std::string_view local : locals) names.erase(local);
  for (std::string_view formal : decl->prop_formals) names.erase(formal);
  ActualsByFormal members = InstanceMembers(names, inst, decl->loc, arena);
  auto substitute = [&members, &arena](Expr*& e) {
    e = SubstituteFormals(e, members, arena);
  };
  ForEachBodySlot(copy->seq_linear, substitute);
  ForEachEventSlot(copy->seq_clock, substitute);
  return copy;
}

void RegisterInstanceCopy(const ModuleItem* member, std::string_view inst,
                          PropertyRegistry& registry, Arena& arena,
                          RunDeclarations run) {
  if (member->kind == ModuleItemKind::kSequenceDecl) {
    ModuleItem* copy = InstanceSequence(member, inst, arena);
    registry.Register(copy);
    run.sequences.push_back(copy);
    return;
  }
  if (member->kind != ModuleItemKind::kPropertyDecl ||
      (member->prop_body_expr == nullptr &&
       member->prop_body_tree == nullptr)) {
    return;
  }
  ModuleItem* copy = InstanceCopy(member, inst, arena);
  registry.Register(copy);
  if (copy->prop_body_tree != nullptr) run.properties.push_back(copy);
}

ModuleItem* ClockedInBlock(const ModuleItem* decl, const ModuleItem* block,
                           Arena& arena) {
  auto* clocked = arena.Create<ModuleItem>(*decl);
  std::string_view own = decl->name.substr(decl->name.rfind('.') + 1);
  clocked->name = *arena.Create<std::string>(std::string(block->name) + "." +
                                             std::string(own));
  if (clocked->kind == ModuleItemKind::kPropertyDecl &&
      clocked->prop_clock.empty()) {
    clocked->prop_clock = block->clocking_event;
  }
  if (clocked->kind == ModuleItemKind::kSequenceDecl &&
      clocked->seq_clock.empty()) {
    clocked->seq_clock = block->clocking_event;
  }
  return clocked;
}

void RegisterInstanceCopies(const ModuleDecl* ifc, std::string_view inst,
                            PropertyRegistry& registry, Arena& arena,
                            RunDeclarations run) {
  for (const ModuleItem* member : ifc->items) {
    if (member->kind != ModuleItemKind::kClockingBlock) {
      RegisterInstanceCopy(member, inst, registry, arena, run);
      continue;
    }
    for (const ModuleItem* decl : member->clocking_decls) {
      RegisterInstanceCopy(ClockedInBlock(decl, member, arena), inst, registry,
                           arena, run);
    }
  }
}

}  // namespace

void RegisterInterfaceInstanceProperties(const ModuleDecl* decl,
                                         const CompilationUnit* unit,
                                         PropertyRegistry& registry,
                                         Arena& arena, RunDeclarations run) {
  if (decl == nullptr || unit == nullptr) return;
  for (const PortDecl& port : decl->ports) {
    if (port.data_type.kind != DataTypeKind::kNamed) continue;
    const ModuleDecl* ifc = FindInterface(port.data_type.type_name, unit);
    if (ifc == nullptr) continue;
    RegisterInstanceCopies(ifc, port.name, registry, arena, run);
  }
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    const ModuleDecl* ifc = FindInterface(item->inst_module, unit);
    if (ifc == nullptr) continue;
    RegisterInstanceCopies(ifc, item->inst_name, registry, arena, run);
  }
}

}  // namespace delta
