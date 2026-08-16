// The check phase of the synthesizer: whether a module describes hardware this
// synthesizer can lower, answered before any of it is lowered. It is held apart
// from the lowering in synth_lower.cpp because the two answer different
// questions about one design, and because a check that reports is what stops a
// netlist being returned over a construct nothing examined.

#include <string>

#include "parser/ast.h"
#include "synthesizer/synth_lower.h"

namespace delta {

// The signal of the first event-control term naming an event variable, or null
// when no term names one. §15.5.2 rules that the `@` operator on a named event
// blocks the process until something triggers it, so there is no hardware net
// to sense.
//
// Stated over a list of terms rather than over a process, because the two
// places that ask are an `always` construct's own sensitivity list and an event
// control written as a statement inside it. Asked of the process alone, the
// statement form fell through to §9.4.2's entry in NonSynthStmtRule and was
// told that an event control is not synthesizable -- the subclause of the
// construct rather than of what it waits on, which sends the reader looking for
// a clock where the source names an event variable.
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
    // A system construct is not design semantics; it refers to simulator
    // functionality, so there is no hardware for it to become.
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
  // §11.4.12 makes each expression written between the braces an operand of the
  // concatenation, and §11.4.12.1 adds the multiplier, so the check reaches
  // them as it reaches the operands of every other operator.
  if (!CheckExprSynthesizable(expr->repeat_count)) return false;
  for (const auto* element : expr->elements) {
    if (!CheckExprSynthesizable(element)) return false;
  }
  return true;
}

// What a statement kind is called in IEEE 1800-2023, and the subclause that
// defines it. A kind that describes hardware has no entry and comes back with
// an empty message. Each kind gets its own sentence because the standard makes
// each a distinct construct: a reader told only that a statement is
// unsynthesizable learns nothing about which rule the design broke.
//
// Every kind BodyContainsEventScheduling names in
// src/elaborator/elaborator_validate_funcchecks.cpp has an entry here. That
// function reads §13.4.3 for a constant function and lists the kinds that
// block or schedule a simulation event, which is exactly the property that
// stops a statement from being hardware, so a kind added there is a kind owed
// an entry here. The set below is properly larger: a parallel block, a disable,
// a disable fork and a forever loop schedule nothing and are still not
// hardware.
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
  // Before NonSynthStmtRule, whose §9.4.2 entry covers every event control
  // including the edge-sensitive ones this synthesizer does lower into
  // flip-flops. A term naming an event variable breaks a different rule and
  // gets the report the sensitivity-list form already gets.
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

// §9.3.1's block item declaration used to be passed over whole. The name it
// introduces has storage MapPorts already reserved from the module's variable
// list, which is what LowersToNothing accounts for, and the value the
// declaration gives that name was read nowhere under src/synthesizer/. So an
// initializer holding one of the expression kinds NonSynthExprRule names --- a
// function call, a cast, a system function --- was reported at once on the
// right of an assignment and passed over in silence on a declaration.
//
// The declared type is answered before the initializer, because it is what the
// design wrote. §9.7 makes `process` a built-in class and process::self() a
// static method returning "a handle to the current process", and no hardware
// holds one, whatever expression the initializer turns out to be.
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

// Whether LowerExprBit would have a lowering for every node of `expr`.
//
// CheckExprSynthesizable answers for §5.6.3's system function and walks the
// operators, and the fourteen kinds NonSynthExprRule names are answered from
// LowerExprBit instead. An initializer never reaches LowerExprBit, because
// LowersToNothing drops the declaration before the statement is lowered, so the
// table is asked here as well. Without it a function call written as an
// initializer stayed silent while the identical expression on the right of an
// assignment was reported, which is the general case behind the process
// declaration above.
//
// The recursion follows the same children CheckExprSynthesizable follows, so
// the two answer over one shape of expression rather than two.
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

// The operands of `expr`, taken as CheckExprSynthesizable takes them, so the
// two walks answer over one shape of expression rather than two.
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
