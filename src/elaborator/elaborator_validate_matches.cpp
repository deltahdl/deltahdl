#include <format>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static void CheckLhsPatternNamedKeys(const Expr* lhs, DiagEngine& diag) {
  if (!lhs) return;
  const Expr* pat = lhs;
  if (pat->kind == ExprKind::kCast && pat->lhs) pat = pat->lhs;
  if (pat->kind == ExprKind::kAssignmentPattern && !pat->pattern_keys.empty()) {
    diag.Error(lhs->range.start,
               "LHS assignment pattern shall use positional notation only");
  }
}

static void WalkStmtsForLhsPatternKeys(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPatternNamedKeys(s->lhs, diag);
  }
  for (auto* sub : s->stmts) WalkStmtsForLhsPatternKeys(sub, diag);
  WalkStmtsForLhsPatternKeys(s->then_branch, diag);
  WalkStmtsForLhsPatternKeys(s->else_branch, diag);
  WalkStmtsForLhsPatternKeys(s->body, diag);
  WalkStmtsForLhsPatternKeys(s->for_body, diag);
  for (auto& ci : s->case_items) WalkStmtsForLhsPatternKeys(ci.body, diag);
}

// §10.9: a positional assignment pattern on the LHS shall hold the same number
// of bits as the RHS supplies. Fire only when both sides have statically known
// widths so that unrelated diagnostics keep their primacy.
static void CheckLhsPatternWidthSum(const Expr* lhs, const Expr* rhs,
                                    const RtlirModule* mod,
                                    const TypedefMap& typedefs,
                                    DiagEngine& diag) {
  if (!lhs || !rhs) return;
  const Expr* pat = lhs;
  if (pat->kind == ExprKind::kCast && pat->lhs) pat = pat->lhs;
  if (pat->kind != ExprKind::kAssignmentPattern) return;
  if (!pat->pattern_keys.empty()) return;
  if (pat->elements.empty()) return;

  uint32_t sum = 0;
  for (const auto* elem : pat->elements) {
    uint32_t w = LookupLhsWidth(elem, mod);
    if (w == 0) return;
    sum += w;
  }
  uint32_t rhs_w = InferExprWidth(rhs, typedefs);
  if (rhs_w == 0) return;
  if (sum == rhs_w) return;

  diag.Error(lhs->range.start,
             std::format("LHS assignment pattern needs {} bits but RHS "
                         "supplies {} bits",
                         sum, rhs_w));
}

static void WalkStmtsForLhsPatternWidths(const Stmt* s, const RtlirModule* mod,
                                         const TypedefMap& typedefs,
                                         DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPatternWidthSum(s->lhs, s->rhs, mod, typedefs, diag);
  }
  for (auto* sub : s->stmts)
    WalkStmtsForLhsPatternWidths(sub, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->then_branch, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->else_branch, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->body, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->for_body, mod, typedefs, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForLhsPatternWidths(ci.body, mod, typedefs, diag);
}

void Elaborator::ValidateLhsPatternWidths(const ModuleDecl* decl,
                                          const RtlirModule* mod) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForLhsPatternWidths(item->body, mod, typedefs_, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckLhsPatternWidthSum(item->assign_lhs, item->assign_rhs, mod,
                              typedefs_, diag_);
    }
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);

    CheckInterconnectProcContAssign(item->body, interconnect_names_, diag_);
    CheckProceduralAssignLhs(item->body, diag_);

    CheckForceLhs(item->body, net_names_, nettype_net_names_, diag_);

    WalkStmtsForLhsPatternKeys(item->body, diag_);
  }
  ValidateEdgeOnReal(item);
  ValidateChandleContAssign(item);
  ValidateChandleSensitivity(item);
  ValidateVirtualInterfaceContAssign(item);
  ValidateVirtualInterfaceSensitivity(item);
  ValidateInterconnectContAssign(item);
  ValidateClassHandleContAssign(item);

  if (item->kind == ModuleItemKind::kNetDecl &&
      (item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
      !item->init_expr) {
    diag_.Error(item->loc,
                "drive strength on net declaration requires an assignment");
  }

  if ((item->kind == ModuleItemKind::kNetDecl ||
       item->kind == ModuleItemKind::kContAssign ||
       item->kind == ModuleItemKind::kGateInst ||
       item->kind == ModuleItemKind::kUdpInst) &&
      item->drive_strength0 == 1 && item->drive_strength1 == 1) {
    diag_.Error(item->loc, "drive strength (highz0, highz1) is illegal");
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
    CheckScalarSelect(item->assign_rhs, scalar_var_names_, diag_);
    CheckScalarSelect(item->assign_lhs, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidth(item->assign_rhs, diag_);
    CheckIndexedPartSelectWidth(item->assign_lhs, diag_);
  }
  if (is_proc && item->body) {
    CheckScalarSelectStmt(item->body, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidthStmt(item->body, diag_);
  }
}

// §12.6: "A constant expression pattern shall be of integral type." Real and
// string literals are the constant expressions that are not integral.
static bool IsNonIntegralConstantPattern(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kRealLiteral) return true;
  if (e->kind == ExprKind::kStringLiteral) return true;
  return false;
}

static void CheckMatchesPattern(const Expr* pat, DiagEngine& diag) {
  if (!pat) return;
  // A `pattern &&& filter_expression` (§12.6.1) wraps the actual pattern on the
  // left; the filter on the right is an ordinary expression, not a pattern.
  const Expr* p = pat;
  if (p->kind == ExprKind::kBinary && p->op == TokenKind::kAmpAmpAmp) {
    p = p->lhs;
  }
  if (IsNonIntegralConstantPattern(p)) {
    diag.Error(p->range.start,
               "constant expression pattern shall be of integral type");
  }
}

static void WalkExprForMatchesOp(const Expr* e, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kKwMatches) {
    CheckMatchesPattern(e->rhs, diag);
  }
  WalkExprForMatchesOp(e->lhs, diag);
  WalkExprForMatchesOp(e->rhs, diag);
  WalkExprForMatchesOp(e->condition, diag);
  WalkExprForMatchesOp(e->true_expr, diag);
  WalkExprForMatchesOp(e->false_expr, diag);
  WalkExprForMatchesOp(e->base, diag);
  WalkExprForMatchesOp(e->index, diag);
  WalkExprForMatchesOp(e->index_end, diag);
  for (auto* a : e->args) WalkExprForMatchesOp(a, diag);
  for (auto* x : e->elements) WalkExprForMatchesOp(x, diag);
}

static void WalkStmtForMatchesPattern(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kCase && s->case_matches) {
    for (const auto& ci : s->case_items) {
      if (ci.is_default) continue;
      for (const auto* pat : ci.patterns) {
        CheckMatchesPattern(pat, diag);
        WalkExprForMatchesOp(pat, diag);
      }
    }
  }
  if (s->condition) WalkExprForMatchesOp(s->condition, diag);
  if (s->expr) WalkExprForMatchesOp(s->expr, diag);
  if (s->lhs) WalkExprForMatchesOp(s->lhs, diag);
  if (s->rhs) WalkExprForMatchesOp(s->rhs, diag);
  if (s->for_cond) WalkExprForMatchesOp(s->for_cond, diag);
  for (auto* sub : s->stmts) WalkStmtForMatchesPattern(sub, diag);
  for (auto* sub : s->fork_stmts) WalkStmtForMatchesPattern(sub, diag);
  WalkStmtForMatchesPattern(s->then_branch, diag);
  WalkStmtForMatchesPattern(s->else_branch, diag);
  WalkStmtForMatchesPattern(s->body, diag);
  WalkStmtForMatchesPattern(s->for_body, diag);
  for (auto& ci : s->case_items) WalkStmtForMatchesPattern(ci.body, diag);
  for (auto& ri : s->randcase_items) WalkStmtForMatchesPattern(ri.second, diag);
}

void Elaborator::ValidateMatchesPatternIntegral(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body) WalkStmtForMatchesPattern(item->body, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts) WalkStmtForMatchesPattern(s, diag_);
    }
  }
}

// §12.6.1: a pattern-matching case statement compares its tested expression
// against the patterns of each item, so the tested expression and the patterns
// must share a known type. A real-valued selector cannot have the same type as
// an integral constant pattern, so the pairing is a static type error.
// Identifier and wildcard patterns (§12.6) match any value and impose no
// integral type, so they are left alone here.
static bool IsIntegralLiteralPattern(const Expr* pat) {
  if (!pat) return false;
  const Expr* p = pat;
  if (p->kind == ExprKind::kBinary && p->op == TokenKind::kAmpAmpAmp) {
    p = p->lhs;
  }
  return p && p->kind == ExprKind::kIntegerLiteral;
}

static void CheckMatchesCaseSelectorType(const Stmt* s, const TypeMap& types,
                                         DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kCase && s->case_matches && s->condition) {
    auto name = ExprIdent(s->condition);
    auto it = types.find(name);
    if (!name.empty() && it != types.end() && IsRealType(it->second)) {
      for (const auto& ci : s->case_items) {
        if (ci.is_default) continue;
        for (const auto* pat : ci.patterns) {
          if (IsIntegralLiteralPattern(pat)) {
            diag.Error(s->condition->range.start,
                       "pattern-matching case selector type differs from the "
                       "type of its integral pattern");
            break;
          }
        }
      }
    }
  }
  for (auto* sub : s->stmts) CheckMatchesCaseSelectorType(sub, types, diag);
  for (auto* sub : s->fork_stmts)
    CheckMatchesCaseSelectorType(sub, types, diag);
  CheckMatchesCaseSelectorType(s->then_branch, types, diag);
  CheckMatchesCaseSelectorType(s->else_branch, types, diag);
  CheckMatchesCaseSelectorType(s->body, types, diag);
  CheckMatchesCaseSelectorType(s->for_body, types, diag);
  for (const auto& ci : s->case_items)
    CheckMatchesCaseSelectorType(ci.body, types, diag);
}

void Elaborator::ValidateMatchesCaseSelectorType(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body)
        CheckMatchesCaseSelectorType(item->body, var_types_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckMatchesCaseSelectorType(s, var_types_, diag_);
    }
  }
}

// §12.6.2: in each `e matches p` clause of an if-else predicate, e and p shall
// have the same statically known type. A real-valued left side cannot share a
// type with an integral constant pattern, so that pairing is a static type
// error. The predicate is a sequential conjunction of clauses joined by `&&&`,
// so each matches operator is reached by descending the `&&&` chain. Identifier
// and wildcard patterns impose no integral type and are left alone.
static void CheckMatchesIfPredicate(const Expr* pred, const TypeMap& types,
                                    DiagEngine& diag) {
  if (!pred || pred->kind != ExprKind::kBinary) return;
  if (pred->op == TokenKind::kAmpAmpAmp) {
    CheckMatchesIfPredicate(pred->lhs, types, diag);
    CheckMatchesIfPredicate(pred->rhs, types, diag);
    return;
  }
  if (pred->op != TokenKind::kKwMatches) return;
  auto name = ExprIdent(pred->lhs);
  auto it = types.find(name);
  if (!name.empty() && it != types.end() && IsRealType(it->second) &&
      IsIntegralLiteralPattern(pred->rhs)) {
    diag.Error(pred->range.start,
               "pattern-matching if predicate value type differs from the "
               "type of its integral pattern");
  }
}

static void CheckMatchesIfPredicateStmt(const Stmt* s, const TypeMap& types,
                                        DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kIf && s->condition) {
    CheckMatchesIfPredicate(s->condition, types, diag);
  }
  for (auto* sub : s->stmts) CheckMatchesIfPredicateStmt(sub, types, diag);
  for (auto* sub : s->fork_stmts) CheckMatchesIfPredicateStmt(sub, types, diag);
  CheckMatchesIfPredicateStmt(s->then_branch, types, diag);
  CheckMatchesIfPredicateStmt(s->else_branch, types, diag);
  CheckMatchesIfPredicateStmt(s->body, types, diag);
  CheckMatchesIfPredicateStmt(s->for_body, types, diag);
  for (const auto& ci : s->case_items)
    CheckMatchesIfPredicateStmt(ci.body, types, diag);
}

void Elaborator::ValidateMatchesIfPredicateType(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body)
        CheckMatchesIfPredicateStmt(item->body, var_types_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckMatchesIfPredicateStmt(s, var_types_, diag_);
    }
  }
}

void Elaborator::ValidateMixedAssignments() {
  for (const auto& [name, loc] : cont_assign_targets_) {
    if (proc_assign_targets_.find(name) != proc_assign_targets_.end()) {
      diag_.Error(loc, std::format("variable '{}' has both continuous and "
                                   "procedural assignments",
                                   name));
    }
  }
  for (const auto& [name, loc] : output_port_targets_) {
    if (cont_assign_targets_.find(name) != cont_assign_targets_.end()) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by both output port and "
                              "continuous assignment",
                              name));
    }
    if (var_init_names_.count(name) != 0) {
      diag_.Error(loc, std::format("variable '{}' driven by output port has an "
                                   "initializer",
                                   name));
    }
    if (proc_assign_targets_.find(name) != proc_assign_targets_.end()) {
      diag_.Error(loc, std::format("variable '{}' driven by output port has "
                                   "procedural assignments",
                                   name));
    }
  }
}

void Elaborator::ValidateInputPortAssignments(const ModuleDecl* decl) {
  for (const auto& port : decl->ports) {
    if (port.direction != Direction::kInput) continue;
    // §23.3.3.2 frames this rule in terms of a variable input port; a net input
    // port driven from inside the module falls under the net rules (§23.3.3.3)
    // instead, so only the variable case is rejected here.
    bool port_is_var =
        !port.data_type.is_net && !port.data_type.is_interconnect;
    if (!port_is_var) continue;

    auto ca = cont_assign_targets_.find(port.name);
    if (ca != cont_assign_targets_.end()) {
      diag_.Error(ca->second,
                  std::format("variable '{}' is declared as an input port and "
                              "cannot be the target of an assignment",
                              port.name));
    }
    auto pa = proc_assign_targets_.find(port.name);
    if (pa != proc_assign_targets_.end()) {
      diag_.Error(pa->second,
                  std::format("variable '{}' is declared as an input port and "
                              "cannot be the target of an assignment",
                              port.name));
    }
  }
}

static void CheckDisableTargets(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kDisable && s->expr &&
      s->expr->kind == ExprKind::kIdentifier) {
    if (func_decls.count(s->expr->text) != 0) {
      diag.Error(s->range.start,
                 "disable statement shall not be used to disable a function");
    }
  }
  for (auto* sub : s->stmts) CheckDisableTargets(sub, func_decls, diag);
  for (auto* sub : s->fork_stmts) CheckDisableTargets(sub, func_decls, diag);
  CheckDisableTargets(s->then_branch, func_decls, diag);
  CheckDisableTargets(s->else_branch, func_decls, diag);
  CheckDisableTargets(s->body, func_decls, diag);
  CheckDisableTargets(s->for_body, func_decls, diag);
  for (auto& ci : s->case_items) CheckDisableTargets(ci.body, func_decls, diag);
  for (auto& ri : s->randcase_items)
    CheckDisableTargets(ri.second, func_decls, diag);
}

void Elaborator::ValidateDisableTargets(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body) CheckDisableTargets(item->body, func_decls_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckDisableTargets(s, func_decls_, diag_);
    }
  }
}

void Elaborator::ValidateProceduralNetAssign() {
  for (const auto& [name, loc] : proc_assign_targets_) {
    if (net_names_.count(name) != 0) {
      diag_.Error(loc, std::format("net '{}' cannot be the target of a "
                                   "procedural assignment",
                                   name));
    }
  }
}

void Elaborator::ValidateDynamicArrayNba(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> dyn_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_dynamic) dyn_names.insert(name);
  }
  if (dyn_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) CheckNbaDynamicArrayTarget(item->body, dyn_names, diag_);
    for (auto* s : item->func_body_stmts)
      CheckNbaDynamicArrayTarget(s, dyn_names, diag_);
  }
}

bool IsArrayQueryFunc(std::string_view callee) {
  return callee == "$left" || callee == "$right" || callee == "$low" ||
         callee == "$high" || callee == "$increment" || callee == "$size" ||
         callee == "$dimensions" || callee == "$unpacked_dimensions";
}

// §20.7 treats a typedef as dynamically sized when one of its unpacked
// dimensions is a dynamic array ([], parsed as a null dimension), a queue
// ([$], a "$" identifier dimension), or a wildcard associative array ([*]).
bool TypedefHasDynamicDim(const std::vector<Expr*>& dims) {
  for (const auto* d : dims) {
    if (d == nullptr) return true;
    if (d->kind == ExprKind::kIdentifier && (d->text == "$" || d->text == "*"))
      return true;
  }
  return false;
}

namespace {

void CheckArrayQueryOnDynamicTypeExpr(
    const Expr* e, const std::unordered_set<std::string_view>& dyn_types,
    DiagEngine& diag) {
  if (!e) return;
  // A bare identifier first argument that names a dynamically sized typedef is
  // the type identifier itself, not an object of that type; querying it has no
  // defined extent.
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      !e->args.empty() && e->args[0] &&
      e->args[0]->kind == ExprKind::kIdentifier &&
      dyn_types.count(e->args[0]->text) != 0) {
    diag.Error(e->range.start,
               std::format("array query function '{}' cannot be applied "
                           "directly to dynamically sized type '{}'",
                           e->callee, e->args[0]->text));
  }
  CheckArrayQueryOnDynamicTypeExpr(e->lhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->rhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->condition, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->true_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->false_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->base, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->index, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->index_end, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->repeat_count, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->with_expr, dyn_types, diag);
  for (auto* a : e->args) CheckArrayQueryOnDynamicTypeExpr(a, dyn_types, diag);
  for (auto* el : e->elements)
    CheckArrayQueryOnDynamicTypeExpr(el, dyn_types, diag);
}

void CheckArrayQueryOnDynamicTypeStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_types,
    DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnDynamicTypeExpr(s->condition, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->lhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->rhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->delay, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->var_init, dyn_types, diag);
  for (auto* sub : s->stmts)
    CheckArrayQueryOnDynamicTypeStmt(sub, dyn_types, diag);
  for (auto* sub : s->fork_stmts)
    CheckArrayQueryOnDynamicTypeStmt(sub, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->then_branch, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->else_branch, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->body, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->for_body, dyn_types, diag);
  for (auto* init : s->for_inits)
    CheckArrayQueryOnDynamicTypeStmt(init, dyn_types, diag);
  for (auto& ci : s->case_items)
    CheckArrayQueryOnDynamicTypeStmt(ci.body, dyn_types, diag);
}

}  // namespace

void Elaborator::ValidateArrayQueryOnDynamicType(const ModuleDecl* decl) {
  // §20.7: the array query functions may not be used directly on a dynamically
  // sized type identifier. Collect such typedef names, then reject any direct
  // query on one.
  std::unordered_set<std::string_view> dyn_types;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        TypedefHasDynamicDim(item->unpacked_dims)) {
      dyn_types.insert(item->name);
    }
  }
  if (dyn_types.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body)
      CheckArrayQueryOnDynamicTypeStmt(item->body, dyn_types, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnDynamicTypeStmt(s, dyn_types, diag_);
    CheckArrayQueryOnDynamicTypeExpr(item->init_expr, dyn_types, diag_);
  }
}

namespace {

// §20.14.1: the seed argument to $random shall be an integral variable. A real
// or string variable cannot hold the integral seed state, so a seed naming one
// is rejected. Other clearly integral kinds (vectors, enums, packed structs)
// are left alone to avoid false positives on legitimate seeds.
bool IsNonIntegralSeedKind(DataTypeKind k) {
  return IsRealType(k) || k == DataTypeKind::kString;
}

void CheckRandomSeedExpr(const Expr* e, const TypeMap& types,
                         DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$random" &&
      !e->args.empty() && e->args[0]) {
    auto name = ExprIdent(e->args[0]);
    if (!name.empty()) {
      auto it = types.find(name);
      if (it != types.end() && IsNonIntegralSeedKind(it->second)) {
        diag.Error(e->range.start,
                   "seed argument of $random shall be an integral variable");
      }
    }
  }
  CheckRandomSeedExpr(e->lhs, types, diag);
  CheckRandomSeedExpr(e->rhs, types, diag);
  CheckRandomSeedExpr(e->condition, types, diag);
  CheckRandomSeedExpr(e->true_expr, types, diag);
  CheckRandomSeedExpr(e->false_expr, types, diag);
  CheckRandomSeedExpr(e->base, types, diag);
  CheckRandomSeedExpr(e->index, types, diag);
  CheckRandomSeedExpr(e->index_end, types, diag);
  CheckRandomSeedExpr(e->repeat_count, types, diag);
  CheckRandomSeedExpr(e->with_expr, types, diag);
  for (auto* a : e->args) CheckRandomSeedExpr(a, types, diag);
  for (auto* el : e->elements) CheckRandomSeedExpr(el, types, diag);
}

void CheckRandomSeedStmt(const Stmt* s, const TypeMap& types,
                         DiagEngine& diag) {
  if (!s) return;
  CheckRandomSeedExpr(s->condition, types, diag);
  CheckRandomSeedExpr(s->lhs, types, diag);
  CheckRandomSeedExpr(s->rhs, types, diag);
  CheckRandomSeedExpr(s->expr, types, diag);
  CheckRandomSeedExpr(s->delay, types, diag);
  CheckRandomSeedExpr(s->var_init, types, diag);
  for (auto* sub : s->stmts) CheckRandomSeedStmt(sub, types, diag);
  for (auto* sub : s->fork_stmts) CheckRandomSeedStmt(sub, types, diag);
  CheckRandomSeedStmt(s->then_branch, types, diag);
  CheckRandomSeedStmt(s->else_branch, types, diag);
  CheckRandomSeedStmt(s->body, types, diag);
  CheckRandomSeedStmt(s->for_body, types, diag);
  for (auto* init : s->for_inits) CheckRandomSeedStmt(init, types, diag);
  for (auto& ci : s->case_items) CheckRandomSeedStmt(ci.body, types, diag);
}

}  // namespace

void Elaborator::ValidateRandomSeedType(const ModuleDecl* decl) {
  // §20.14.1: enforce that any $random seed argument naming a module variable
  // refers to an integral variable.
  for (const auto* item : decl->items) {
    if (item->body) CheckRandomSeedStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckRandomSeedStmt(s, var_types_, diag_);
    CheckRandomSeedExpr(item->init_expr, var_types_, diag_);
  }
}

}  // namespace delta
