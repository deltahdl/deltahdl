#include <format>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

// --- §11.2.2: Aggregate expression comparison validation ---

// §11.2.2: Check a single binary expression for aggregate type mismatch.
void Elaborator::CheckAggregateCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  if (expr->lhs->kind != ExprKind::kIdentifier) return;
  if (expr->rhs->kind != ExprKind::kIdentifier) return;
  auto lit = var_named_types_.find(expr->lhs->text);
  auto rit = var_named_types_.find(expr->rhs->text);
  if (lit == var_named_types_.end() || rit == var_named_types_.end()) return;
  if (lit->second == rit->second) return;

  auto is_aggregate_var = [&](std::string_view name,
                              std::string_view type_name) {
    if (var_array_info_.count(name)) return true;
    auto it = typedefs_.find(type_name);
    return it != typedefs_.end() && IsAggregateType(it->second);
  };
  if (!is_aggregate_var(expr->lhs->text, lit->second)) return;
  if (!is_aggregate_var(expr->rhs->text, rit->second)) return;

  diag_.Error(expr->range.start,
              std::format("comparison of non-equivalent aggregate "
                          "types '{}' and '{}'",
                          lit->second, rit->second));
}

void Elaborator::WalkExprForAggregateCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary &&
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq)) {
    CheckAggregateCompareOp(expr);
  }
  WalkExprForAggregateCompare(expr->lhs);
  WalkExprForAggregateCompare(expr->rhs);
  WalkExprForAggregateCompare(expr->condition);
  WalkExprForAggregateCompare(expr->true_expr);
  WalkExprForAggregateCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForAggregateCompare(elem);
  for (auto* arg : expr->args) WalkExprForAggregateCompare(arg);
}

void Elaborator::WalkStmtsForAggregateCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForAggregateCompare(s->rhs);
  WalkExprForAggregateCompare(s->lhs);
  WalkExprForAggregateCompare(s->expr);
  WalkExprForAggregateCompare(s->condition);
  WalkExprForAggregateCompare(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForAggregateCompare(sub);
  WalkStmtsForAggregateCompare(s->then_branch);
  WalkStmtsForAggregateCompare(s->else_branch);
  WalkStmtsForAggregateCompare(s->body);
  WalkStmtsForAggregateCompare(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAggregateCompare(ci.body);
}

void Elaborator::ValidateAggregateComparisons(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForAggregateCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAggregateCompare(item->assign_rhs);
    }
  }
}

// --- §11.3.1: Operators not permitted on real operands ---

static bool IsRealVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && IsRealType(it->second);
}

// Operators illegal on real/shortreal operands per Table 11-1.
static bool IsIllegalOnReal(TokenKind op) {
  switch (op) {
    // Case equality
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    // Wildcard equality
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
    // Bitwise binary
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
    // Shift
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
    // Modulus
    case TokenKind::kPercent:
      return true;
    default:
      return false;
  }
}

// Unary operators illegal on real operands.
static bool IsUnaryIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

void Elaborator::WalkExprForRealOps(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool lhs_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    bool rhs_real = expr->rhs && IsRealVar(expr->rhs, var_types_);
    if ((lhs_real || rhs_real) && IsIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  "operator is not allowed on real operands");
    }
  }
  if (expr->kind == ExprKind::kUnary) {
    bool operand_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    if (operand_real && IsUnaryIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  "operator is not allowed on real operands");
    }
  }
  WalkExprForRealOps(expr->lhs);
  WalkExprForRealOps(expr->rhs);
  WalkExprForRealOps(expr->condition);
  WalkExprForRealOps(expr->true_expr);
  WalkExprForRealOps(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForRealOps(elem);
  for (auto* arg : expr->args) WalkExprForRealOps(arg);
}

void Elaborator::WalkStmtsForRealOps(const Stmt* s) {
  if (!s) return;
  WalkExprForRealOps(s->rhs);
  WalkExprForRealOps(s->lhs);
  WalkExprForRealOps(s->expr);
  WalkExprForRealOps(s->condition);
  WalkExprForRealOps(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForRealOps(sub);
  WalkStmtsForRealOps(s->then_branch);
  WalkStmtsForRealOps(s->else_branch);
  WalkStmtsForRealOps(s->body);
  WalkStmtsForRealOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForRealOps(ci.body);
}

void Elaborator::ValidateRealOperatorRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForRealOps(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForRealOps(item->assign_rhs);
    }
  }
}

// --- §11.3.6: Assignment-in-expression restrictions ---

static bool IsAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kEq:
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

void Elaborator::WalkExprForAssignInExpr(const Expr* expr,
                                         bool in_event_or_cont) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary && IsAssignOp(expr->op)) {
    if (in_event_or_cont) {
      diag_.Error(expr->range.start,
                  "assignment operator within expression is illegal in "
                  "this context");
    }
  }
  WalkExprForAssignInExpr(expr->lhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->rhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->condition, in_event_or_cont);
  WalkExprForAssignInExpr(expr->true_expr, in_event_or_cont);
  WalkExprForAssignInExpr(expr->false_expr, in_event_or_cont);
  for (auto* elem : expr->elements)
    WalkExprForAssignInExpr(elem, in_event_or_cont);
  for (auto* arg : expr->args) WalkExprForAssignInExpr(arg, in_event_or_cont);
}

void Elaborator::WalkStmtsForAssignInExpr(const Stmt* s) {
  if (!s) return;
  // §11.3.6: assignment operator is illegal in a procedural continuous
  // assignment expression.
  if (s->kind == StmtKind::kAssign && s->rhs) {
    WalkExprForAssignInExpr(s->rhs, true);
  }
  for (auto* sub : s->stmts) WalkStmtsForAssignInExpr(sub);
  WalkStmtsForAssignInExpr(s->then_branch);
  WalkStmtsForAssignInExpr(s->else_branch);
  WalkStmtsForAssignInExpr(s->body);
  WalkStmtsForAssignInExpr(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssignInExpr(ci.body);
}

void Elaborator::ValidateAssignInExprRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      for (const auto& ev : item->sensitivity) {
        WalkExprForAssignInExpr(ev.signal, true);
      }
      if (item->body) WalkStmtsForAssignInExpr(item->body);
    }
    if (item->kind == ModuleItemKind::kInitialBlock && item->body) {
      WalkStmtsForAssignInExpr(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAssignInExpr(item->assign_rhs, true);
    }
  }
}

// §10.11: Validate alias statement operands.
static std::string_view AliasNetIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

void Elaborator::ValidateAlias(const ModuleItem* item) {
  std::unordered_set<std::string_view> seen;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!seen.insert(name).second) {
      diag_.Error(item->loc, std::format("net '{}' aliased to itself", name));
    }
  }
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!net_names_.count(name) && declared_names_.count(name)) {
      diag_.Error(item->loc,
                  std::format("'{}' is a variable, not a net; "
                              "variables cannot appear in alias statements",
                              name));
    }
  }
}

// §10.10.3: Check a single assignment for nested concatenation in unpacked
// array context.
void Elaborator::CheckArrayConcatNestingInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.elem_type == DataTypeKind::kString) return;
  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kConcatenation) {
      diag_.Error(elem->range.start,
                  "nested concatenation in unpacked array "
                  "concatenation is not self-determined");
    }
  }
}

// §10.10.3: Validate nesting of unpacked array concatenations.
void Elaborator::WalkStmtsForArrayConcatNesting(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayConcatNestingInAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForArrayConcatNesting(sub);
  WalkStmtsForArrayConcatNesting(s->then_branch);
  WalkStmtsForArrayConcatNesting(s->else_branch);
  WalkStmtsForArrayConcatNesting(s->body);
  WalkStmtsForArrayConcatNesting(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayConcatNesting(ci.body);
}

void Elaborator::ValidateUnpackedArrayConcatNesting(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForArrayConcatNesting(item->body);
    }
  }
}

// --- §11.4.12: Unsized constants not allowed in concatenations ---

void Elaborator::WalkExprForUnsizedInConcat(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kConcatenation) {
    for (auto* elem : expr->elements) {
      if (elem->kind == ExprKind::kIntegerLiteral) {
        auto tick = elem->text.find('\'');
        if (tick == std::string_view::npos || tick == 0) {
          diag_.Error(elem->range.start,
                      "unsized constant is not allowed in a concatenation");
        }
      }
    }
  }
  WalkExprForUnsizedInConcat(expr->lhs);
  WalkExprForUnsizedInConcat(expr->rhs);
  WalkExprForUnsizedInConcat(expr->condition);
  WalkExprForUnsizedInConcat(expr->true_expr);
  WalkExprForUnsizedInConcat(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForUnsizedInConcat(elem);
  for (auto* arg : expr->args) WalkExprForUnsizedInConcat(arg);
}

void Elaborator::WalkStmtsForUnsizedInConcat(const Stmt* s) {
  if (!s) return;
  WalkExprForUnsizedInConcat(s->rhs);
  WalkExprForUnsizedInConcat(s->lhs);
  WalkExprForUnsizedInConcat(s->expr);
  WalkExprForUnsizedInConcat(s->condition);
  WalkExprForUnsizedInConcat(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForUnsizedInConcat(sub);
  WalkStmtsForUnsizedInConcat(s->then_branch);
  WalkStmtsForUnsizedInConcat(s->else_branch);
  WalkStmtsForUnsizedInConcat(s->body);
  WalkStmtsForUnsizedInConcat(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForUnsizedInConcat(ci.body);
}

void Elaborator::ValidateUnsizedInConcat(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForUnsizedInConcat(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForUnsizedInConcat(item->assign_lhs);
      WalkExprForUnsizedInConcat(item->assign_rhs);
    }
    if (item->init_value) {
      WalkExprForUnsizedInConcat(item->init_value);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForUnsizedInConcat(p.init_value);
  }
}

// --- §11.4.12: Select of concatenation shall not be an lvalue ---

static bool IsSelectOnConcat(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kSelect) return false;
  const Expr* base = expr->lhs;
  while (base && base->kind == ExprKind::kSelect) base = base->lhs;
  return base && base->kind == ExprKind::kConcatenation;
}

void Elaborator::CheckSelectOnConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (IsSelectOnConcat(lhs)) {
    diag_.Error(lhs->range.start,
                "select of a concatenation shall not be used as an lvalue");
  }
  if (lhs->kind == ExprKind::kConcatenation) {
    for (auto* elem : lhs->elements) CheckSelectOnConcatLvalue(elem);
  }
}

void Elaborator::WalkStmtsForSelectOnConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckSelectOnConcatLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForSelectOnConcatLvalue(sub);
  WalkStmtsForSelectOnConcatLvalue(s->then_branch);
  WalkStmtsForSelectOnConcatLvalue(s->else_branch);
  WalkStmtsForSelectOnConcatLvalue(s->body);
  WalkStmtsForSelectOnConcatLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForSelectOnConcatLvalue(ci.body);
}

void Elaborator::ValidateSelectOnConcatLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForSelectOnConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckSelectOnConcatLvalue(item->assign_lhs);
    }
  }
}

// --- §11.4.12.1: Replication shall not appear on the LHS of an assignment ---

static bool ExprContainsReplicate(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kReplicate) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ExprContainsReplicate(elem)) return true;
    }
  }
  return false;
}

void Elaborator::CheckReplicateLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (ExprContainsReplicate(lhs)) {
    diag_.Error(lhs->range.start,
                "replication shall not appear on the left-hand side "
                "of an assignment");
  }
}

void Elaborator::WalkStmtsForReplicateLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckReplicateLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForReplicateLvalue(sub);
  WalkStmtsForReplicateLvalue(s->then_branch);
  WalkStmtsForReplicateLvalue(s->else_branch);
  WalkStmtsForReplicateLvalue(s->body);
  WalkStmtsForReplicateLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForReplicateLvalue(ci.body);
}

void Elaborator::ValidateReplicateLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForReplicateLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckReplicateLvalue(item->assign_lhs);
    }
  }
}

// --- §11.4.12.1: Replication multiplier constraints ---

static bool RepeatCountHasXZ(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIntegerLiteral) {
    auto apos = e->text.find('\'');
    if (apos != std::string_view::npos) {
      return e->text.substr(apos + 1).find_first_of("xXzZ") !=
             std::string_view::npos;
    }
  }
  return false;
}

void Elaborator::WalkExprForReplicateMultiplier(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kReplicate) {
    const Expr* rc = expr->repeat_count;
    if (RepeatCountHasXZ(rc)) {
      diag_.Error(rc->range.start,
                  "replication multiplier shall not contain x or z");
    } else {
      auto val = ConstEvalInt(rc);
      if (val) {
        if (*val < 0) {
          diag_.Error(rc->range.start,
                      "replication multiplier shall not be negative");
        } else if (*val == 0) {
          // Zero is only valid inside a concatenation with other operands.
          // A standalone zero replication is checked here: the parent must
          // be a concatenation (which is ensured by the caller context).
          // We flag standalone uses — the enclosing expression check below
          // handles the case where {0{x}} appears as a top-level expression
          // rather than inside a concatenation.
        }
      }
    }
  }
  WalkExprForReplicateMultiplier(expr->lhs);
  WalkExprForReplicateMultiplier(expr->rhs);
  WalkExprForReplicateMultiplier(expr->condition);
  WalkExprForReplicateMultiplier(expr->true_expr);
  WalkExprForReplicateMultiplier(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForReplicateMultiplier(elem);
  for (auto* arg : expr->args) WalkExprForReplicateMultiplier(arg);
}

static bool IsZeroReplicate(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kReplicate) return false;
  auto val = ConstEvalInt(expr->repeat_count);
  return val && *val == 0;
}

static void CheckZeroReplicateStandalone(const Expr* expr,
                                         DiagEngine& diag) {
  if (!expr) return;
  if (IsZeroReplicate(expr)) {
    diag.Error(expr->range.start,
               "zero replication shall appear only within a concatenation "
               "in which at least one operand has a positive size");
  }
  if (expr->kind == ExprKind::kConcatenation) {
    // Inside a concatenation, zero replication is OK as long as at least one
    // other operand has positive size. Since a concatenation requires at
    // least one element, and the only way ALL operands could have zero size
    // is if every element is a zero replication, we check that.
    bool all_zero = true;
    for (const auto* elem : expr->elements) {
      if (!IsZeroReplicate(elem)) {
        all_zero = false;
        break;
      }
    }
    if (all_zero && !expr->elements.empty()) {
      diag.Error(expr->range.start,
                 "zero replication shall appear only within a concatenation "
                 "in which at least one operand has a positive size");
    }
    // Recurse into non-zero elements (but not into the zero replication
    // elements, which are valid here).
    for (const auto* elem : expr->elements) {
      if (!IsZeroReplicate(elem)) {
        CheckZeroReplicateStandalone(elem, diag);
      }
    }
    return;
  }
  CheckZeroReplicateStandalone(expr->lhs, diag);
  CheckZeroReplicateStandalone(expr->rhs, diag);
  CheckZeroReplicateStandalone(expr->condition, diag);
  CheckZeroReplicateStandalone(expr->true_expr, diag);
  CheckZeroReplicateStandalone(expr->false_expr, diag);
  for (const auto* elem : expr->elements)
    CheckZeroReplicateStandalone(elem, diag);
  for (const auto* arg : expr->args)
    CheckZeroReplicateStandalone(arg, diag);
}

static void WalkStmtsForZeroReplicateStandalone(const Stmt* s,
                                                DiagEngine& diag) {
  if (!s) return;
  CheckZeroReplicateStandalone(s->rhs, diag);
  CheckZeroReplicateStandalone(s->lhs, diag);
  CheckZeroReplicateStandalone(s->expr, diag);
  CheckZeroReplicateStandalone(s->condition, diag);
  CheckZeroReplicateStandalone(s->assert_expr, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForZeroReplicateStandalone(sub, diag);
  WalkStmtsForZeroReplicateStandalone(s->then_branch, diag);
  WalkStmtsForZeroReplicateStandalone(s->else_branch, diag);
  WalkStmtsForZeroReplicateStandalone(s->body, diag);
  WalkStmtsForZeroReplicateStandalone(s->for_body, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForZeroReplicateStandalone(ci.body, diag);
}

void Elaborator::WalkStmtsForReplicateMultiplier(const Stmt* s) {
  if (!s) return;
  WalkExprForReplicateMultiplier(s->rhs);
  WalkExprForReplicateMultiplier(s->lhs);
  WalkExprForReplicateMultiplier(s->expr);
  WalkExprForReplicateMultiplier(s->condition);
  WalkExprForReplicateMultiplier(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForReplicateMultiplier(sub);
  WalkStmtsForReplicateMultiplier(s->then_branch);
  WalkStmtsForReplicateMultiplier(s->else_branch);
  WalkStmtsForReplicateMultiplier(s->body);
  WalkStmtsForReplicateMultiplier(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForReplicateMultiplier(ci.body);
}

void Elaborator::ValidateReplicateMultiplier(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForReplicateMultiplier(item->body);
      WalkStmtsForZeroReplicateStandalone(item->body, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForReplicateMultiplier(item->assign_lhs);
      WalkExprForReplicateMultiplier(item->assign_rhs);
      CheckZeroReplicateStandalone(item->assign_lhs, diag_);
      CheckZeroReplicateStandalone(item->assign_rhs, diag_);
    }
    if (item->init_value) {
      WalkExprForReplicateMultiplier(item->init_value);
      CheckZeroReplicateStandalone(item->init_value, diag_);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForReplicateMultiplier(p.init_value);
    CheckZeroReplicateStandalone(p.init_value, diag_);
  }
}

// --- §11.4.12.2: String concatenation shall not appear on the LHS ---

bool Elaborator::ConcatContainsStringElement(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    auto it = var_types_.find(expr->text);
    return it != var_types_.end() && it->second == DataTypeKind::kString;
  }
  if (expr->kind == ExprKind::kStringLiteral) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ConcatContainsStringElement(elem)) return true;
    }
  }
  return false;
}

void Elaborator::CheckStringConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (lhs->kind != ExprKind::kConcatenation) return;
  if (ConcatContainsStringElement(lhs)) {
    diag_.Error(lhs->range.start,
                "string concatenation is not allowed on the left-hand side "
                "of an assignment");
  }
}

void Elaborator::WalkStmtsForStringConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckStringConcatLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForStringConcatLvalue(sub);
  WalkStmtsForStringConcatLvalue(s->then_branch);
  WalkStmtsForStringConcatLvalue(s->else_branch);
  WalkStmtsForStringConcatLvalue(s->body);
  WalkStmtsForStringConcatLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForStringConcatLvalue(ci.body);
}

void Elaborator::ValidateStringConcatLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForStringConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringConcatLvalue(item->assign_lhs);
    }
  }
}

}  // namespace delta
