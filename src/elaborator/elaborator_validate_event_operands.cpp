#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

// What a trigger (§15.5.1, printed page 378) and a wait_order (§15.5.4,
// printed page 379) name: a named event, the only thing either acts on.

namespace delta {

namespace {

// The kinds the module's variables and nets are declared with, and the names
// a block or a subroutine declares for itself, which hide them (§23.9) and
// are left unjudged.
struct EventOperandScope {
  const TypeMap& kinds;
  NameSet hidden;
};

// The name an operand is written under: the identifier it is, or the one a
// select of an element of an array of events starts with; empty for any
// other operand, a member or a hierarchical name among them.
std::string_view OperandName(const Expr* e) {
  while (e->kind == ExprKind::kSelect) e = e->base;
  return e->kind == ExprKind::kIdentifier ? e->text : std::string_view();
}

// Reports `operand`, written as `what`, where a declaration of the module
// gives it a kind other than event. A named type is left alone, as a typedef
// of event is one.
void ReportNonEvent(const Expr* operand, const EventOperandScope& scope,
                    std::string_view what, std::string_view subclause,
                    DiagEngine& diag) {
  const std::string_view kName = OperandName(operand);
  if (kName.empty() || scope.hidden.contains(kName)) return;
  const auto kFound = scope.kinds.find(kName);
  if (kFound == scope.kinds.end() || kFound->second == DataTypeKind::kEvent ||
      kFound->second == DataTypeKind::kNamed) {
    return;
  }
  diag.Error(operand->range.start,
             std::format("{} '{}' is not a named event", what, kName),
             Subclause(subclause));
}

void ReportNonEventOperandsIn(const Stmt* s, EventOperandScope& scope,
                              DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) scope.hidden.insert(s->var_name);
  if (s->kind == StmtKind::kEventTrigger ||
      s->kind == StmtKind::kNbEventTrigger) {
    ReportNonEvent(s->expr, scope, "trigger target", "15.5.1", diag);
  }
  for (const Expr* operand : s->wait_order_events) {
    ReportNonEvent(operand, scope, "wait_order operand", "15.5.4", diag);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { ReportNonEventOperandsIn(sub, scope, diag); });
}

}  // namespace

void ReportNonEventOperands(const ModuleDecl* decl, const TypeMap& kinds,
                            DiagEngine& diag) {
  for (const ModuleItem* item : decl->items) {
    EventOperandScope scope{kinds, {}};
    if (IsProceduralItemKind(item->kind)) {
      ReportNonEventOperandsIn(item->body, scope, diag);
    }
    for (const auto& arg : item->func_args) scope.hidden.insert(arg.name);
    for (const Stmt* s : item->func_body_stmts) {
      ReportNonEventOperandsIn(s, scope, diag);
    }
  }
}

}  // namespace delta
