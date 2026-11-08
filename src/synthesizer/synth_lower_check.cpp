#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "synthesizer/synth_lower.h"

namespace delta {

const Expr* NamedEventTerm(const std::vector<EventExpr>& events,
                           const RtlirModule* mod) {
  for (const auto& ev : events) {
    const Expr* sig = ev.signal;
    if (!sig || sig->kind != ExprKind::kIdentifier) continue;
    for (const auto& var : mod->variables) {
      if (var.name == sig->text) {
        if (var.is_event) return sig;
        break;
      }
    }
  }
  return nullptr;
}

bool SynthLower::CheckExprSynthesizable(const Expr* expr) {
  if (!expr) return true;
  if (expr->kind == ExprKind::kSystemCall) {
    diag_.Error(expr->range.start,
                "system task or system function '" + std::string(expr->callee) +
                    "' is not synthesizable",
                Subclause("5.6.3"));
    return false;
  }
  if (expr->kind == ExprKind::kUnary || expr->kind == ExprKind::kBinary) {
    return CheckExprSynthesizable(expr->lhs) &&
           CheckExprSynthesizable(expr->rhs);
  }
  if (expr->kind == ExprKind::kTernary) {
    return CheckExprSynthesizable(expr->condition) &&
           CheckExprSynthesizable(expr->true_expr) &&
           CheckExprSynthesizable(expr->false_expr);
  }
  if (expr->kind == ExprKind::kConcatenation ||
      expr->kind == ExprKind::kReplicate) {
    return CheckElementsSynthesizable(expr);
  }
  return true;
}

bool SynthLower::CheckElementsSynthesizable(const Expr* expr) {
  if (!CheckExprSynthesizable(expr->repeat_count)) return false;
  for (const auto* element : expr->elements) {
    if (!CheckExprSynthesizable(element)) return false;
  }
  return true;
}

static NonSynthRule NonSynthStmtRule(StmtKind kind) {
  switch (kind) {
    case StmtKind::kFork:
      return {"parallel block is not synthesizable", "9.3.2"};
    case StmtKind::kTimingControl:
      return {"procedural timing control is not synthesizable", "9.4"};
    case StmtKind::kDelay:
      return {"delay control is not synthesizable", "9.4.1"};
    case StmtKind::kEventControl:
      return {"event control is not synthesizable", "9.4.2"};
    case StmtKind::kWait:
      return {"wait statement is not synthesizable", "9.4.3"};
    case StmtKind::kWaitFork:
      return {"wait fork statement is not synthesizable", "9.6.1"};
    case StmtKind::kDisable:
      return {"disable statement is not synthesizable", "9.6.2"};
    case StmtKind::kDisableFork:
      return {"disable fork statement is not synthesizable", "9.6.3"};
    case StmtKind::kForever:
      return {"forever loop is not synthesizable", "12.7.6"};
    case StmtKind::kCycleDelay:
      return {"cycle delay is not synthesizable", "14.11"};
    case StmtKind::kEventTrigger:
      return {"event trigger is not synthesizable", "15.5.1"};
    case StmtKind::kNbEventTrigger:
      return {"nonblocking event trigger is not synthesizable", "15.5.1"};
    case StmtKind::kWaitOrder:
      return {"wait_order construct is not synthesizable", "15.5.4"};
    case StmtKind::kExpect:
      return {"expect statement is not synthesizable", "16.17"};
    default:
      return {};
  }
}

bool SynthLower::CheckStmtSynthesizable(const Stmt* stmt,
                                        const RtlirModule* mod) {
  if (!stmt) return true;
  if (stmt->kind == StmtKind::kEventControl) {
    if (const Expr* ev = NamedEventTerm(stmt->events, mod)) {
      diag_.Error(ev->range.start,
                  "named event in event control is not synthesizable",
                  Subclause("15.5.2"));
      return false;
    }
  }
  NonSynthRule rule = NonSynthStmtRule(stmt->kind);
  if (!rule.message.empty()) {
    diag_.Error(stmt->range.start, std::string(rule.message),
                Subclause(rule.subclause));
    return false;
  }
  if (stmt->kind == StmtKind::kExprStmt) {
    return CheckExprSynthesizable(stmt->expr);
  }
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    return CheckExprSynthesizable(stmt->rhs);
  }
  if (stmt->kind == StmtKind::kBlock) {
    return CheckBlockStmts(stmt, mod);
  }
  if (stmt->kind == StmtKind::kIf) {
    return CheckIfSynth(stmt, mod);
  }
  if (stmt->kind == StmtKind::kCase) {
    return CheckCaseSynth(stmt, mod);
  }
  if (stmt->kind == StmtKind::kVarDecl ||
      stmt->kind == StmtKind::kBlockItemDecl) {
    return CheckDeclSynthesizable(stmt);
  }
  return true;
}

bool SynthLower::CheckDeclSynthesizable(const Stmt* stmt) {
  if (stmt->var_decl_type.kind == DataTypeKind::kNamed &&
      stmt->var_decl_type.type_name == "process") {
    diag_.Error(stmt->range.start,
                "a process control handle has no lowering in the synthesizer",
                Subclause("9.7"));
    return false;
  }
  if (!CheckExprSynthesizable(stmt->var_init)) return false;
  return CheckInitializerLowerable(stmt->var_init);
}

bool SynthLower::CheckInitializerLowerable(const Expr* expr) {
  if (!expr) return true;
  NonSynthRule rule = expr->kind == ExprKind::kMemberAccess
                          ? DottedNameRule(expr)
                          : NonSynthExprRule(expr->kind);
  if (!rule.message.empty()) {
    diag_.Error(expr->range.start, std::string(rule.message),
                Subclause(rule.subclause));
    return false;
  }
  return CheckInitializerOperands(expr);
}

bool SynthLower::CheckInitializerOperands(const Expr* expr) {
  if (expr->kind == ExprKind::kUnary || expr->kind == ExprKind::kBinary) {
    return CheckInitializerLowerable(expr->lhs) &&
           CheckInitializerLowerable(expr->rhs);
  }
  if (expr->kind == ExprKind::kTernary) {
    return CheckInitializerLowerable(expr->condition) &&
           CheckInitializerLowerable(expr->true_expr) &&
           CheckInitializerLowerable(expr->false_expr);
  }
  if (expr->kind != ExprKind::kConcatenation &&
      expr->kind != ExprKind::kReplicate) {
    return true;
  }
  if (!CheckInitializerLowerable(expr->repeat_count)) return false;
  for (const auto* element : expr->elements) {
    if (!CheckInitializerLowerable(element)) return false;
  }
  return true;
}

bool SynthLower::CheckBlockStmts(const Stmt* stmt, const RtlirModule* mod) {
  for (const auto* s : stmt->stmts) {
    if (!CheckStmtSynthesizable(s, mod)) return false;
  }
  return true;
}

bool SynthLower::CheckIfSynth(const Stmt* stmt, const RtlirModule* mod) {
  return CheckExprSynthesizable(stmt->condition) &&
         CheckStmtSynthesizable(stmt->then_branch, mod) &&
         CheckStmtSynthesizable(stmt->else_branch, mod);
}

bool SynthLower::CheckCaseSynth(const Stmt* stmt, const RtlirModule* mod) {
  for (const auto& ci : stmt->case_items) {
    if (!CheckStmtSynthesizable(ci.body, mod)) return false;
  }
  return true;
}

}  // namespace delta
