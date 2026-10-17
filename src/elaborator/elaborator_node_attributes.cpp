#include "elaborator/elaborator_node_attributes.h"

#include <functional>
#include <optional>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
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

// Whether an item of `kind` keeps the attributes it is written with nowhere
// but RtlirModule::node_attrs. A net's, a variable's, an instance's, a
// continuous assignment's and a procedure's are kept on their own records.
bool KeepsNodeAttributes(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
    case ModuleItemKind::kSpecparam:
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

// What resolving attributes works with: where they are kept, where a
// duplicate is reported, and the parameter scope, built the first time an
// attribute asks for it.
struct NodeAttributeRecord {
  RtlirNodeAttributes& table;
  DiagEngine& diag;
  const std::function<ScopeMap()>& params;
  std::optional<ScopeMap> scope;

  void Record(const void* node, const std::vector<Attribute>& attrs) {
    if (attrs.empty()) return;
    if (!scope.has_value()) scope = params();
    table[node] = ResolveAttributes(attrs, diag, *scope);
  }

  // §11.3 with §5.12: an operator written with attributes, and those the
  // expressions it holds are written with.
  void RecordExpr(const Expr* expr) {
    if (expr == nullptr) return;
    Record(expr, expr->attrs);
    ForEachExprChild(expr, [this](const Expr* sub) { RecordExpr(sub); });
  }

  // §12.1 with §5.12: a statement written with attributes, and those the
  // statements and expressions it holds are written with.
  void RecordStmt(const Stmt* stmt) {
    if (stmt == nullptr) return;
    Record(stmt, stmt->attrs);
    ForEachChildExpr(stmt, [this](const Expr* expr) { RecordExpr(expr); });
    ForEachChildStmt(stmt, [this](const Stmt* sub) { RecordStmt(sub); });
  }

  // §8.3 with §5.12: a class written with attributes, and its items written
  // with them.
  void RecordClass(const ClassDecl* decl) {
    if (decl == nullptr) return;
    Record(decl, decl->attrs);
    for (const ClassMember* member : decl->members) {
      Record(member, member->attrs);
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
  record.RecordClass(item.class_decl);
}

void RecordDesignClassAttributes(RtlirDesign& design, DiagEngine& diag,
                                 const ScopeMap& params) {
  const std::function<ScopeMap()> kParams = [&params] { return params; };
  NodeAttributeRecord record{design.node_attrs, diag, kParams, std::nullopt};
  for (const ClassDecl* decl : design.cu_class_decls) record.RecordClass(decl);
  for (const PackageDecl* pkg : design.packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item != nullptr) record.RecordClass(item->class_decl);
    }
  }
}

}  // namespace delta
