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

// What resolving one module item's attributes works with: where they are
// kept, where a duplicate is reported, and the parameter scope, built the
// first time an attribute asks for it.
struct NodeAttributeRecord {
  RtlirModule& mod;
  DiagEngine& diag;
  const std::function<ScopeMap()>& params;
  std::optional<ScopeMap> scope;

  void Record(const void* node, const std::vector<Attribute>& attrs) {
    if (attrs.empty()) return;
    if (!scope.has_value()) scope = params();
    mod.node_attrs[node] = ResolveAttributes(attrs, diag, *scope);
  }

  // §12.1 with §5.12: a statement written with attributes, and those the
  // statements it holds are written with.
  void RecordStmt(const Stmt* stmt) {
    if (stmt == nullptr) return;
    Record(stmt, stmt->attrs);
    ForEachChildStmt(stmt, [this](const Stmt* sub) { RecordStmt(sub); });
  }
};

}  // namespace

void RecordNodeAttributes(const ModuleItem& item, RtlirModule& mod,
                          DiagEngine& diag,
                          const std::function<ScopeMap()>& params) {
  NodeAttributeRecord record{mod, diag, params, std::nullopt};
  if (KeepsNodeAttributes(item.kind)) record.Record(&item, item.attrs);
  record.RecordStmt(item.body);
  for (const Stmt* stmt : item.func_body_stmts) record.RecordStmt(stmt);
}

}  // namespace delta
