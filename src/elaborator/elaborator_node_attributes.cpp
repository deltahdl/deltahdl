#include "elaborator/elaborator_node_attributes.h"

#include <functional>
#include <optional>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/constant_scope.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

bool KeepsNodeAttributes(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
      return true;
    default:
      return false;
  }
}

void LayerClassParams(const ClassDecl& decl, ConstantScope& scope) {
  for (const auto& [name, value] : decl.params) {
    if (decl.type_param_names.count(name) == 0) scope.Declare(name, value);
  }
  for (const ClassMember* member : decl.members) {
    if (member->kind == ClassMemberKind::kProperty && member->is_param) {
      scope.Declare(member->name, member->init_expr);
    }
  }
}

struct NodeAttributeRecord {
  RtlirNodeAttributes& table;
  DiagEngine& diag;
  const std::function<ScopeMap()>& params;
  std::optional<ConstantScope> scope;

  ConstantScope& Scope() {
    if (!scope.has_value()) {
      ScopeMap module_params = params();
      scope = ConstantScope{module_params, std::move(module_params)};
    }
    return *scope;
  }

  void Record(const void* node, const std::vector<Attribute>& attrs) {
    if (attrs.empty()) return;
    const ConstantScope& in_force = Scope();
    table[node] =
        ResolveAttributes(attrs, diag, in_force.fold, in_force.constants);
  }

  void RecordExpr(const Expr* expr) {
    if (expr == nullptr) return;
    Record(expr, expr->attrs);
    ForEachExprChild(expr, [this](const Expr* sub) { RecordExpr(sub); });
  }

  void RecordStmt(const Stmt* stmt) {
    if (stmt == nullptr) return;
    Record(stmt, stmt->attrs);
    ForEachChildExpr(stmt, [this](const Expr* expr) { RecordExpr(expr); });
    if (DeclaresParam(stmt)) Scope().Declare(stmt->var_name, stmt->var_init);
    std::optional<ConstantScope> outer;
    if (BlockDeclaresParam(*stmt)) outer = Scope();
    ForEachChildStmt(stmt, [this](const Stmt* sub) { RecordStmt(sub); });
    if (outer.has_value()) scope = std::move(outer);
  }

  void RecordConstraintItem(const ConstraintItem* item) {
    if (item == nullptr) return;
    RecordExpr(item->expr);
    for (const ConstraintDistItem& dist : item->dist) {
      for (const Expr* expr :
           {dist.value, dist.lo, dist.hi, dist.tolerance, dist.weight}) {
        RecordExpr(expr);
      }
    }
    for (const Expr* expr : item->exprs) RecordExpr(expr);
    for (const Expr* expr : item->after) RecordExpr(expr);
    for (const ConstraintItem* sub : item->body) RecordConstraintItem(sub);
    for (const ConstraintItem* sub : item->else_body) RecordConstraintItem(sub);
  }

  void RecordClass(const ClassDecl* decl) {
    if (decl == nullptr) return;
    Record(decl, decl->attrs);
    ConstantScope& in_class = Scope();
    ConstantScope outer = in_class;
    LayerClassParams(*decl, in_class);
    for (const Expr* arg : decl->extends_args) RecordExpr(arg);
    for (const ClassMember* member : decl->members) {
      Record(member, member->attrs);
      for (const Expr* expr : member->constraint_exprs) RecordExpr(expr);
      for (const ConstraintItem* item : member->constraint_items) {
        RecordConstraintItem(item);
      }
    }
    scope = std::move(outer);
  }

  void RecordEvents(const std::vector<EventExpr>& events) {
    for (const EventExpr& event : events) {
      RecordExpr(event.signal);
      RecordExpr(event.iff_condition);
    }
  }

  void RecordProperty(const PropertyExprNode* node) {
    if (node == nullptr) return;
    RecordExpr(node->boolean);
    RecordExpr(node->range_min);
    RecordExpr(node->range_max);
    for (const std::vector<Expr*>& values : node->case_values) {
      for (const Expr* value : values) RecordExpr(value);
    }
    RecordEvents(node->clock);
    for (const PropertyExprNode* operand : node->operands) {
      RecordProperty(operand);
    }
  }

  void RecordPropertyItem(const ModuleItem& item) {
    RecordEvents(item.prop_clock);
    RecordExpr(item.prop_disable_iff);
    RecordProperty(item.prop_body_tree);
  }

  void RecordClocking(const ModuleItem& item) {
    RecordEvents(item.clocking_event);
    for (const ClockingSignalDecl& signal : item.clocking_signals) {
      RecordExpr(signal.skew_delay);
      RecordExpr(signal.out_skew_delay);
      RecordExpr(signal.hier_expr);
    }
  }
};

}  // namespace

void RecordNodeAttributes(const ModuleItem& item, RtlirModule& mod,
                          DiagEngine& diag,
                          const std::function<ScopeMap()>& params) {
  NodeAttributeRecord record{mod.node_attrs, diag, params, std::nullopt};
  if (KeepsNodeAttributes(item.kind)) record.Record(&item, item.attrs);
  record.RecordStmt(item.body);
  for (const Stmt* stmt : item.func_body_stmts) record.RecordStmt(stmt);
  record.RecordExpr(item.assign_lhs);
  record.RecordExpr(item.assign_rhs);
  record.RecordExpr(item.init_expr);
  for (const Expr* terminal : item.gate_terminals) record.RecordExpr(terminal);
  for (const auto& [name, connection] : item.inst_ports) {
    record.RecordExpr(connection);
  }
  record.RecordClocking(item);
  record.RecordPropertyItem(item);
  record.RecordClass(item.class_decl);
}

void RecordModportAttributes(RtlirModule& mod, DiagEngine& diag,
                             const std::function<ScopeMap()>& params) {
  NodeAttributeRecord record{mod.node_attrs, diag, params, std::nullopt};
  for (const ModportDecl* decl : mod.modports) {
    for (const ModportPort& port : decl->ports) record.RecordExpr(port.expr);
  }
}

void RecordDesignAttributes(RtlirDesign& design, DiagEngine& diag,
                            const ScopeMap& params) {
  const std::function<ScopeMap()> kParams = [&params] { return params; };
  NodeAttributeRecord record{design.node_attrs, diag, kParams, std::nullopt};
  for (const ClassDecl* decl : design.cu_class_decls) record.RecordClass(decl);
  for (const PackageDecl* pkg : design.packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item == nullptr) continue;
      record.RecordClass(item->class_decl);
      record.RecordPropertyItem(*item);
    }
  }
}

}  // namespace delta
