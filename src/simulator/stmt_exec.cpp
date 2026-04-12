#include "simulator/stmt_exec.h"

#include <cstdint>
#include <iostream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

// --- Randcase (IEEE §18.16) ---

static ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t total_weight = 0;
  for (const auto& item : stmt->randcase_items) {
    total_weight += EvalExpr(item.first, ctx, arena).ToUint64();
  }
  if (total_weight == 0) {
    ctx.GetDiag().Warning(stmt->range.start,
                          "randcase: all weights are zero; no branch selected");
    co_return StmtResult::kDone;
  }

  uint64_t pick = ctx.Urandom32() % total_weight;
  uint64_t cumulative = 0;
  for (const auto& item : stmt->randcase_items) {
    cumulative += EvalExpr(item.first, ctx, arena).ToUint64();
    if (pick < cumulative) {
      co_return co_await ExecStmt(item.second, ctx, arena);
    }
  }
  co_return StmtResult::kDone;
}

// --- Randsequence (IEEE §18.17) ---

// Forward declare so recursive calls work.
static ExecTask ExecRsProduction(const Stmt* stmt, std::string_view name,
                                 SimContext& ctx, Arena& arena);

static const RsProduction* FindProduction(const Stmt* stmt,
                                          std::string_view name) {
  for (const auto& prod : stmt->rs_productions) {
    if (prod.name == name) return &prod;
  }
  return nullptr;
}

// Forward declare ExecRsProd for mutual recursion.
static ExecTask ExecRsProd(const Stmt* stmt, const RsProd& prod,
                           SimContext& ctx, Arena& arena);

static ExecTask ExecRsProdIf(const Stmt* stmt, const RsProd& prod,
                             SimContext& ctx, Arena& arena) {
  if (EvalExpr(prod.condition, ctx, arena).ToUint64() != 0) {
    co_return co_await ExecRsProduction(stmt, prod.if_true.name, ctx, arena);
  }
  if (prod.has_else) {
    co_return co_await ExecRsProduction(stmt, prod.if_false.name, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProdRepeat(const Stmt* stmt, const RsProd& prod,
                                 SimContext& ctx, Arena& arena) {
  auto count = EvalExpr(prod.repeat_count, ctx, arena).ToUint64();
  for (uint64_t i = 0; i < count; ++i) {
    auto result =
        co_await ExecRsProduction(stmt, prod.repeat_item.name, ctx, arena);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProdCase(const Stmt* stmt, const RsProd& prod,
                               SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(prod.case_expr, ctx, arena).ToUint64();
  for (const auto& ci : prod.case_items) {
    if (ci.is_default) {
      co_return co_await ExecRsProduction(stmt, ci.item.name, ctx, arena);
    }
    for (auto* pat : ci.patterns) {
      if (EvalExpr(pat, ctx, arena).ToUint64() == val) {
        co_return co_await ExecRsProduction(stmt, ci.item.name, ctx, arena);
      }
    }
  }
  co_return StmtResult::kDone;
}

// Execute a single rs_prod item.
static ExecTask ExecRsProd(const Stmt* stmt, const RsProd& prod,
                           SimContext& ctx, Arena& arena) {
  switch (prod.kind) {
    case RsProdKind::kCodeBlock:
      for (auto* s : prod.code_stmts) {
        auto result = co_await ExecStmt(s, ctx, arena);
        if (result == StmtResult::kBreak || result == StmtResult::kReturn) {
          co_return result;
        }
      }
      co_return StmtResult::kDone;
    case RsProdKind::kItem:
      co_return co_await ExecRsProduction(stmt, prod.item.name, ctx, arena);
    case RsProdKind::kIf:
      co_return co_await ExecRsProdIf(stmt, prod, ctx, arena);
    case RsProdKind::kRepeat:
      co_return co_await ExecRsProdRepeat(stmt, prod, ctx, arena);
    case RsProdKind::kCase:
      co_return co_await ExecRsProdCase(stmt, prod, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// Select a rule from a production by weighted random.
static const RsRule& SelectRule(const RsProduction& production, SimContext& ctx,
                                Arena& arena) {
  if (production.rules.size() <= 1) return production.rules[0];
  uint64_t total_weight = 0;
  for (const auto& rule : production.rules) {
    total_weight +=
        rule.weight ? EvalExpr(rule.weight, ctx, arena).ToUint64() : 1;
  }
  if (total_weight == 0) return production.rules[0];
  uint64_t pick = ctx.Urandom32() % total_weight;
  uint64_t cumulative = 0;
  for (const auto& rule : production.rules) {
    cumulative +=
        rule.weight ? EvalExpr(rule.weight, ctx, arena).ToUint64() : 1;
    if (pick < cumulative) return rule;
  }
  return production.rules[0];
}

// Execute rand join production items.
static ExecTask ExecRandJoinItems(const Stmt* stmt, const RsRule& selected,
                                  SimContext& ctx, Arena& arena) {
  for (const auto& item : selected.rand_join_items) {
    auto result = co_await ExecRsProduction(stmt, item.name, ctx, arena);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
    if (result == StmtResult::kReturn) co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

// Execute a rule's production list.
static ExecTask ExecRuleProds(const Stmt* stmt, const RsRule& selected,
                              SimContext& ctx, Arena& arena) {
  for (const auto& prod : selected.prods) {
    auto result = co_await ExecRsProd(stmt, prod, ctx, arena);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
    if (result == StmtResult::kReturn) co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

// Execute a selected rule's weight code and production list.
static ExecTask ExecSelectedRule(const Stmt* stmt, const RsRule& selected,
                                 SimContext& ctx, Arena& arena) {
  for (auto* s : selected.weight_code) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kBreak || result == StmtResult::kReturn) {
      co_return result;
    }
  }
  if (selected.is_rand_join) {
    co_return co_await ExecRandJoinItems(stmt, selected, ctx, arena);
  }
  co_return co_await ExecRuleProds(stmt, selected, ctx, arena);
}

// Execute a named production: select a rule, then run it.
static ExecTask ExecRsProduction(const Stmt* stmt, std::string_view name,
                                 SimContext& ctx, Arena& arena) {
  const auto* production = FindProduction(stmt, name);
  if (!production) co_return StmtResult::kDone;
  const auto& selected = SelectRule(*production, ctx, arena);
  co_return co_await ExecSelectedRule(stmt, selected, ctx, arena);
}

static ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (stmt->rs_productions.empty()) co_return StmtResult::kDone;

  // Determine top production.
  std::string_view top = stmt->rs_top_production;
  if (top.empty()) top = stmt->rs_productions[0].name;

  auto result = co_await ExecRsProduction(stmt, top, ctx, arena);
  // Break from randsequence just terminates it (not outer loops).
  (void)result;
  co_return StmtResult::kDone;
}

// --- Container coroutines (return ExecTask, support suspension) ---

static ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool named = !stmt->label.empty();
  if (named) ctx.PushStaticScope(stmt->label);
  for (auto* s : stmt->stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result != StmtResult::kDone) {
      if (named) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
    if (ctx.StopRequested()) {
      if (named) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
  }
  if (named) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// --- If with unique/priority qualifiers ---

struct UniqueIfResult {
  const Stmt* first_match = nullptr;
  int match_count = 0;
  bool has_final_else = false;
};

static UniqueIfResult EvalUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  UniqueIfResult result;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    auto cond = EvalExpr(cur->condition, ctx, arena);
    if (cond.IsTruthy()) {
      result.match_count++;
      if (!result.first_match) result.first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      result.has_final_else = true;
    }
  }
  return result;
}

static const Stmt* FindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

static ExecTask ExecUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             SimContext& ctx, Arena& arena) {
  auto info = EvalUniqueIfChain(stmt, ctx, arena);

  if (info.match_count > 1) {
    ctx.AddPendingViolation("unique if: multiple conditions matched");
  }
  if (info.first_match) {
    co_return co_await ExecStmt(info.first_match->then_branch, ctx, arena);
  }
  if (info.has_final_else) {
    const Stmt* final_else = FindFinalElse(stmt);
    if (final_else) co_return co_await ExecStmt(final_else, ctx, arena);
  }
  if (!info.has_final_else && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation("unique if: no condition matched");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecPriorityIf(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    auto cond = EvalExpr(cur->condition, ctx, arena);
    if (cond.IsTruthy()) {
      co_return co_await ExecStmt(cur->then_branch, ctx, arena);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FindFinalElse(stmt);
    if (final_else) co_return co_await ExecStmt(final_else, ctx, arena);
  }
  if (!has_final_else) {
    ctx.AddPendingViolation("priority if: no condition matched");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto qual = stmt->qualifier;

  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    auto r = co_await ExecUniqueIf(stmt, qual, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (qual == CaseQualifier::kPriority) {
    auto r = co_await ExecPriorityIf(stmt, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }

  auto cond = EvalExpr(stmt->condition, ctx, arena);
  if (cond.IsTruthy()) {
    auto r = co_await ExecStmt(stmt->then_branch, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (stmt->else_branch) {
    auto r = co_await ExecStmt(stmt->else_branch, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// --- Case matching helpers ---

// Check if a bit position has X or Z in a Logic4Vec.
static bool BitIsZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  bool a = (v.words[wi].aval >> bi) & 1;
  bool b = (v.words[wi].bval >> bi) & 1;
  return a && b;  // Z: aval=1, bval=1
}

static bool BitIsXZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  return (v.words[wi].bval >> bi) & 1;  // bval=1 means X or Z
}

using BitPredicate = bool (*)(const Logic4Vec&, uint32_t);

static bool CaseDontCareMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                              BitPredicate skip_bit) {
  uint32_t width = (sel.width > pat.width) ? sel.width : pat.width;
  for (uint32_t i = 0; i < width; ++i) {
    if (skip_bit(sel, i) || skip_bit(pat, i)) continue;
    uint32_t swi = i / 64, sbi = i % 64;
    uint32_t pwi = i / 64, pbi = i % 64;
    bool sa = (swi < sel.nwords) && ((sel.words[swi].aval >> sbi) & 1);
    bool pa = (pwi < pat.nwords) && ((pat.words[pwi].aval >> pbi) & 1);
    if (sa != pa) return false;
  }
  return true;
}

static bool CasexMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsXZ);
}

static bool CasezMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsZ);
}

// §12.5.4: Asymmetric wildcard value match — x/z in pattern are don't-cares,
// x/z in selector produce no match.
static bool CaseInsideValueMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  if (!sel.IsKnown()) return false;
  uint32_t nw = (sel.nwords > pat.nwords) ? sel.nwords : pat.nwords;
  for (uint32_t i = 0; i < nw; ++i) {
    uint64_t sa = (i < sel.nwords) ? sel.words[i].aval : 0;
    uint64_t pa = (i < pat.nwords) ? pat.words[i].aval : 0;
    uint64_t pb = (i < pat.nwords) ? pat.words[i].bval : 0;
    // pb marks x/z bits in pattern — those are don't-cares.
    if ((sa ^ pa) & ~pb) return false;
  }
  return true;
}

// §12.5.4: Range match for case-inside (plain range, $ bounds, tolerance).
static bool CaseInsideRangeMatch(const Logic4Vec& sel, const Expr* pat,
                                 SimContext& ctx, Arena& arena) {
  if (!sel.IsKnown()) return false;
  uint64_t sv = sel.ToUint64();
  // Tolerance ranges [A +/- B] and [A +%- B].
  if (pat->op == TokenKind::kPlusSlashMinus ||
      pat->op == TokenKind::kPlusPercentMinus) {
    auto a_v = EvalExpr(pat->index, ctx, arena);
    auto b_v = EvalExpr(pat->index_end, ctx, arena);
    if (!a_v.IsKnown() || !b_v.IsKnown()) return false;
    uint64_t a = a_v.ToUint64();
    uint64_t b = b_v.ToUint64();
    uint64_t tol = b;
    if (pat->op == TokenKind::kPlusPercentMinus) tol = a * b / 100;
    uint64_t lo = (a >= tol) ? a - tol : 0;
    uint64_t hi = a + tol;
    if (lo > hi) { uint64_t t = lo; lo = hi; hi = t; }
    return sv >= lo && sv <= hi;
  }
  // Normal range [lo:hi] with possible $ bounds.
  auto is_dollar = [](const Expr* e) {
    return e->kind == ExprKind::kIdentifier && e->text == "$";
  };
  uint64_t lo = is_dollar(pat->index)
                    ? 0
                    : EvalExpr(pat->index, ctx, arena).ToUint64();
  uint64_t hi = is_dollar(pat->index_end)
                    ? ((sel.width >= 64) ? ~uint64_t{0}
                                         : (uint64_t{1} << sel.width) - 1)
                    : EvalExpr(pat->index_end, ctx, arena).ToUint64();
  if (lo > hi) { uint64_t t = lo; lo = hi; hi = t; }
  return sv >= lo && sv <= hi;
}

// §12.5.4: Check if a case-inside pattern matches (value or range).
static bool CaseInsidePatternMatch(const Logic4Vec& sel, const Expr* pat,
                                   SimContext& ctx, Arena& arena) {
  if (pat->kind == ExprKind::kSelect && pat->index && pat->index_end)
    return CaseInsideRangeMatch(sel, pat, ctx, arena);
  auto pat_val = EvalExpr(pat, ctx, arena);
  return CaseInsideValueMatch(sel, pat_val);
}

// §12.5: 4-state exact comparison — each bit must match exactly (0, 1, x, z).
static bool CaseExactMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  uint32_t nw = (sel.nwords > pat.nwords) ? sel.nwords : pat.nwords;
  for (uint32_t i = 0; i < nw; ++i) {
    uint64_t sa = (i < sel.nwords) ? sel.words[i].aval : 0;
    uint64_t sb = (i < sel.nwords) ? sel.words[i].bval : 0;
    uint64_t pa = (i < pat.nwords) ? pat.words[i].aval : 0;
    uint64_t pb = (i < pat.nwords) ? pat.words[i].bval : 0;
    if (sa != pa || sb != pb) return false;
  }
  return true;
}

// §12.6: Pattern match — x/z in pattern are wildcards.
// casez matches additionally treats z in selector as wildcard;
// casex matches treats x/z in both as wildcards.
static bool CaseMatchesMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                             TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseInsideValueMatch(sel, pat);
}

// §12.6.1: Check a case-matches pattern, handling &&& guard expressions.
static bool CaseMatchesPatternMatch(const Logic4Vec& sel, const Expr* pat_expr,
                                    SimContext& ctx, Arena& arena,
                                    TokenKind case_kind) {
  // §12.6.1: pattern &&& guard — pattern must match AND guard must be true.
  if (pat_expr->kind == ExprKind::kBinary &&
      pat_expr->op == TokenKind::kAmpAmpAmp) {
    auto pat_val = EvalExpr(pat_expr->lhs, ctx, arena);
    if (!CaseMatchesMatch(sel, pat_val, case_kind)) return false;
    auto guard = EvalExpr(pat_expr->rhs, ctx, arena);
    return guard.IsTruthy();
  }
  auto pv = EvalExpr(pat_expr, ctx, arena);
  return CaseMatchesMatch(sel, pv, case_kind);
}

// Check if a case item matches based on case_kind (non-inside, non-matches).
static bool CaseItemMatches(const Logic4Vec& sel, const Logic4Vec& pat,
                            TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseExactMatch(sel, pat);
}

// --- Case with casex/casez/inside and qualifiers ---

static bool CasePatternMatch(const Logic4Vec& sel, const Expr* pat,
                             const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->case_inside) return CaseInsidePatternMatch(sel, pat, ctx, arena);
  if (stmt->case_matches)
    return CaseMatchesPatternMatch(sel, pat, ctx, arena, stmt->case_kind);
  return CaseItemMatches(sel, EvalExpr(pat, ctx, arena), stmt->case_kind);
}

static bool CaseItemHasMatch(const Logic4Vec& sel, const CaseItem& item,
                             const Stmt* stmt, SimContext& ctx, Arena& arena) {
  for (auto* pat : item.patterns) {
    if (CasePatternMatch(sel, pat, stmt, ctx, arena)) return true;
  }
  return false;
}

static const Stmt* FindCaseDefault(const Stmt* stmt) {
  for (const auto& item : stmt->case_items) {
    if (item.is_default) return item.body;
  }
  return nullptr;
}

struct UniqueCaseResult {
  const Stmt* first_match_body = nullptr;
  int match_count = 0;
  bool has_default = false;
};

static UniqueCaseResult ScanUniqueCaseItems(const Logic4Vec& sel,
                                            const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  UniqueCaseResult result;
  for (const auto& item : stmt->case_items) {
    if (item.is_default) {
      result.has_default = true;
      continue;
    }
    if (CaseItemHasMatch(sel, item, stmt, ctx, arena)) {
      result.match_count++;
      if (!result.first_match_body) result.first_match_body = item.body;
    }
  }
  return result;
}

static ExecTask ExecUniqueCase(const Stmt* stmt, const Logic4Vec& sel,
                               CaseQualifier qual, SimContext& ctx,
                               Arena& arena) {
  auto info = ScanUniqueCaseItems(sel, stmt, ctx, arena);

  if (info.match_count > 1) {
    ctx.AddPendingViolation("unique case: multiple items matched");
  }
  if (info.first_match_body) {
    co_return co_await ExecStmt(info.first_match_body, ctx, arena);
  }
  auto* default_body = FindCaseDefault(stmt);
  if (default_body) co_return co_await ExecStmt(default_body, ctx, arena);
  if (!info.has_default && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation("unique case: no matching item found");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecStandardCase(const Stmt* stmt, const Logic4Vec& sel,
                                 CaseQualifier qual, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    if (CaseItemHasMatch(sel, item, stmt, ctx, arena)) {
      co_return co_await ExecStmt(item.body, ctx, arena);
    }
  }
  auto* default_body = FindCaseDefault(stmt);
  if (default_body) co_return co_await ExecStmt(default_body, ctx, arena);
  if (qual == CaseQualifier::kPriority) {
    ctx.AddPendingViolation("priority case: no matching item found");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto qual = stmt->qualifier;
  auto sel = EvalExpr(stmt->condition, ctx, arena);

  StmtResult r;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = co_await ExecUniqueCase(stmt, sel, qual, ctx, arena);
  } else {
    r = co_await ExecStandardCase(stmt, sel, qual, ctx, arena);
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return r;
}

// --- Loops ---

// Create for-init variables when the init declares a type (§12.7.1).
static void CreateForInitVars(const Stmt* stmt, SimContext& ctx) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    if (i >= stmt->for_init_types.size()) break;
    if (stmt->for_init_types[i].kind == DataTypeKind::kImplicit) continue;
    auto* init = stmt->for_inits[i];
    if (!init || !init->lhs) continue;
    uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
    if (w == 0) w = 32;
    ctx.CreateLocalVariable(init->lhs->text, w);
  }
}

static bool HasTypedForInit(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

static ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  bool scoped = HasTypedForInit(stmt);
  if (scoped) ctx.PushScope();
  CreateForInitVars(stmt, ctx);
  for (auto* init : stmt->for_inits)
    co_await ExecStmt(init, ctx, arena);
  while (!ctx.StopRequested()) {
    if (stmt->for_cond) {
      auto cond = EvalExpr(stmt->for_cond, ctx, arena);
      if (!cond.IsTruthy()) break;
    }
    auto result = co_await ExecStmt(stmt->for_body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (scoped) ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
    for (auto* step : stmt->for_steps)
      co_await ExecStmt(step, ctx, arena);
  }
  if (scoped) ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (!cond.IsTruthy()) break;
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto count_val = EvalExpr(stmt->condition, ctx, arena);
  uint64_t count = count_val.IsKnown() ? count_val.ToUint64() : 0;
  for (uint64_t i = 0; i < count && !ctx.StopRequested(); ++i) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  do {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (!cond.IsTruthy()) break;
  } while (!ctx.StopRequested());
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// --- Foreach (IEEE §12.7.3) ---

static std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

static uint32_t GetArraySize(const Stmt* stmt, SimContext& ctx) {
  std::string name = GetForeachArrayName(stmt->expr);
  if (name.empty()) return 0;
  auto* info = ctx.FindArrayInfo(name);
  if (info) return info->size;
  auto* var = ctx.FindVariable(name);
  if (!var) return 0;
  return var->value.width;
}

static ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::string arr_name = GetForeachArrayName(stmt->expr);
  if (!arr_name.empty()) {
    auto* aa = ctx.FindAssocArray(arr_name);
    if (aa && aa->is_wildcard) {
      ctx.GetDiag().Error(
          {}, "foreach not allowed on wildcard associative array '" +
                  arr_name + "'");
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
  }
  uint32_t size = GetArraySize(stmt, ctx);
  if (size == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  // Determine loop variable name (first non-empty foreach_vars entry).
  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size && !ctx.StopRequested(); ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(arena, 32, i);
    }
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }

  ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// --- Delay ---

static ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  uint32_t cycles = 0;
  if (stmt->cycle_delay) {
    auto val = EvalExpr(stmt->cycle_delay, ctx, arena);
    cycles = static_cast<uint32_t>(val.ToUint64());
  }
  if (cycles > 0) {
    co_await CycleDelayAwaiter{ctx, cycles};
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    auto val = EvalExpr(stmt->delay, ctx, arena);
    ticks = val.ToUint64();
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Event control ---

static bool IsNamedEvent(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return false;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return false;
  if (!ev.signal || ev.signal->kind != ExprKind::kIdentifier) return false;
  auto* var = ctx.FindVariable(ev.signal->text);
  return var && var->is_event;
}

static ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->events.empty()) {
    if (IsNamedEvent(stmt, ctx)) {
      co_await NamedEventAwaiter{ctx, stmt->events[0].signal->text};
    } else {
      co_await EventAwaiter{ctx, stmt->events, arena};
    }
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Event trigger (->ev) ---

static StmtResult ExecEventTriggerImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return StmtResult::kDone;
  // §15.5.5.2: Triggering a null event shall have no effect.
  if (var->is_null_event) return StmtResult::kDone;
  // §15.5.3: Set sticky triggered state for this timeslot.
  ctx.SetEventTriggered(stmt->expr->text);
  // §9.4.2: Schedule triggered processes in Active region rather than
  // running them inline, so the triggering process continues first.
  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = std::move(cb);
    sched.ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  }
  return StmtResult::kDone;
}

// --- Nonblocking event trigger (->>ev) ---

static StmtResult ExecNbEventTriggerImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return StmtResult::kDone;
  // §15.5.5.2: Triggering a null event shall have no effect.
  if (var->is_null_event) return StmtResult::kDone;

  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();

  // §15.5.1: Schedule the trigger in the NBA region.
  auto event_name = stmt->expr->text;
  auto& sched = ctx.GetScheduler();
  auto time = ctx.CurrentTime();
  time.ticks += delay;

  auto* nba_event = sched.GetEventPool().Acquire();
  nba_event->callback = [var, event_name, &ctx]() {
    ctx.SetEventTriggered(event_name);
    auto pending = std::move(var->watchers);
    var->watchers.clear();
    auto& s = ctx.GetScheduler();
    for (auto& cb : pending) {
      auto* ev = s.GetEventPool().Acquire();
      ev->callback = std::move(cb);
      s.ScheduleEvent(ctx.CurrentTime(), Region::kActive, ev);
    }
  };
  sched.ScheduleEvent(time, Region::kNBA, nba_event);
  return StmtResult::kDone;
}

// --- Wait (IEEE §9.4.3) ---

static ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::unordered_set<std::string> reads;
  CollectExprReads(stmt->condition, reads);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() != 0) break;
    if (read_vars.empty()) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
  if (stmt->body) {
    auto r = co_await ExecStmt(stmt->body, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// --- wait_order (IEEE §15.5.4) ---

// Awaiter that watches multiple event variables and reports which one
// triggered first. A shared done flag prevents double-resume when stale
// watchers on unconsumed events fire later.
struct WaitOrderStepAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& event_names;
  std::string_view triggered_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto done = std::make_shared<bool>(false);
    auto* out = &triggered_name;

    for (auto name : event_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->AddWatcher([h, name, out, done]() mutable {
        if (*done) return true;
        *done = true;
        *out = name;
        h.resume();
        return true;
      });
    }
  }

  std::string_view await_resume() const noexcept { return triggered_name; }
};

static ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto& events = stmt->wait_order_events;
  if (events.empty()) {
    if (stmt->then_branch) {
      co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
    }
    co_return StmtResult::kDone;
  }

  bool failed = false;

  for (size_t i = 0; i < events.size() && !failed; ++i) {
    auto expected_name = events[i]->text;

    // §15.5.4: Only the first event can use persistent triggered state.
    if (i == 0 && ctx.IsEventTriggered(expected_name)) {
      continue;
    }

    // Collect event names from this position onwards.
    std::vector<std::string_view> remaining;
    for (size_t j = i; j < events.size(); ++j) {
      remaining.push_back(events[j]->text);
    }

    auto triggered = co_await WaitOrderStepAwaiter{ctx, remaining, {}};

    if (triggered != expected_name) {
      failed = true;
    }
  }

  if (failed) {
    if (stmt->else_branch) {
      co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
    }
    // §15.5.4: No else clause — generate default runtime error.
    ctx.GetDiag().Error({}, "wait_order failure: events triggered out of order");
    co_return StmtResult::kDone;
  }

  if (stmt->then_branch) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Fork/join (IEEE §9.3.2) ---

static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, ForkJoinState* state) {
  co_await ExecStmt(body, ctx, arena);
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    state->parent.resume();
  }
}

static bool IsForkBlockItemDecl(const Stmt* s) {
  return s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl;
}

static ExecTask ExecFork(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  if (stmt->fork_stmts.empty()) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  // §9.3.2: Initialize block_item_declaration variables before spawning.
  uint32_t process_count = 0;
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) {
      co_await ExecStmt(s, ctx, arena);
    } else {
      process_count++;
    }
  }

  if (process_count == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  auto* state = arena.Create<ForkJoinState>();
  state->remaining = process_count;
  state->join_any = (stmt->join_kind == TokenKind::kKwJoinAny);

  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) continue;
    auto* p = arena.Create<Process>();
    p->kind = ProcessKind::kInitial;
    p->coro = ForkChildCoroutine(s, ctx, arena, state).Release();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [p]() { p->Resume(); };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  }

  if (stmt->join_kind != TokenKind::kKwJoinNone) {
    co_await ForkJoinAwaiter{state};
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// --- Immediate assertions (§16.3) ---

static ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);
  if (cond.ToUint64() != 0) {
    // Pass action.
    if (stmt->assert_pass_stmt) {
      co_return co_await ExecStmt(stmt->assert_pass_stmt, ctx, arena);
    }
  } else {
    // Fail action.
    if (stmt->assert_fail_stmt) {
      co_return co_await ExecStmt(stmt->assert_fail_stmt, ctx, arena);
    } else if (stmt->kind != StmtKind::kCoverImmediate) {
      // §16.3: Default $error when assert/assume fails with no else clause.
      ctx.IncrementAssertionFailCount();
      std::cerr << "ERROR: Assertion failed.\n";
    }
  }
  co_return StmtResult::kDone;
}

// §13: Inline task call — executes task body through coroutine dispatcher.
static ExecTask ExecInlineTaskCall(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* expr = stmt->expr;
  auto* func = SetupTaskCall(expr, ctx, arena);
  if (!func) {
    EvalExpr(expr, ctx, arena);
    co_return StmtResult::kDone;
  }
  for (auto* s : func->func_body_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kReturn) break;
  }
  TeardownTaskCall(func, expr, ctx, arena);
  co_return StmtResult::kDone;
}

// §10.4.1: Blocking assignment with intra-assignment delay.
// Evaluates RHS before the delay, then assigns after the delay.
static ExecTask ExecBlockingAssignTimed(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  auto delay_val = EvalExpr(stmt->delay, ctx, arena);
  co_await DelayAwaiter{ctx, delay_val.ToUint64()};
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

// --- Main dispatch ---

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt) return ExecTask::Immediate(StmtResult::kDone);

  switch (stmt->kind) {
    case StmtKind::kNull:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBlock:
      return ExecBlock(stmt, ctx, arena);
    case StmtKind::kIf:
      return ExecIf(stmt, ctx, arena);
    case StmtKind::kCase:
      return ExecCase(stmt, ctx, arena);
    case StmtKind::kFor:
      return ExecFor(stmt, ctx, arena);
    case StmtKind::kForeach:
      return ExecForeach(stmt, ctx, arena);
    case StmtKind::kWhile:
      return ExecWhile(stmt, ctx, arena);
    case StmtKind::kForever:
      return ExecForever(stmt, ctx, arena);
    case StmtKind::kRepeat:
      return ExecRepeat(stmt, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecDoWhile(stmt, ctx, arena);
    case StmtKind::kBlockingAssign:
      if (stmt->delay) return ExecBlockingAssignTimed(stmt, ctx, arena);
      return ExecTask::Immediate(ExecBlockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kNonblockingAssign:
      return ExecTask::Immediate(ExecNonblockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kExprStmt:
      return ExecInlineTaskCall(stmt, ctx, arena);
    case StmtKind::kDelay:
      return ExecDelay(stmt, ctx, arena);
    case StmtKind::kCycleDelay:
      return ExecCycleDelay(stmt, ctx, arena);
    case StmtKind::kEventControl:
      return ExecEventControl(stmt, ctx, arena);
    case StmtKind::kFork:
      return ExecFork(stmt, ctx, arena);
    case StmtKind::kWait:
      return ExecWait(stmt, ctx, arena);
    case StmtKind::kEventTrigger:
      return ExecTask::Immediate(ExecEventTriggerImpl(stmt, ctx));
    case StmtKind::kNbEventTrigger:
      return ExecTask::Immediate(ExecNbEventTriggerImpl(stmt, ctx, arena));
    case StmtKind::kWaitOrder:
      return ExecWaitOrder(stmt, ctx, arena);
    case StmtKind::kTimingControl:
    case StmtKind::kDisable:
    case StmtKind::kDisableFork:
    case StmtKind::kWaitFork:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBreak:
      return ExecTask::Immediate(StmtResult::kBreak);
    case StmtKind::kContinue:
      return ExecTask::Immediate(StmtResult::kContinue);
    case StmtKind::kReturn:
      return ExecTask::Immediate(StmtResult::kReturn);
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      return ExecImmediateAssert(stmt, ctx, arena);
    case StmtKind::kForce:
    case StmtKind::kAssign:
      return ExecTask::Immediate(ExecForceOrAssignImpl(stmt, ctx, arena));
    case StmtKind::kRelease:
    case StmtKind::kDeassign:
      return ExecTask::Immediate(ExecReleaseOrDeassignImpl(stmt, ctx));
    case StmtKind::kRandcase:
      return ExecRandcase(stmt, ctx, arena);
    case StmtKind::kRandsequence:
      return ExecRandsequence(stmt, ctx, arena);
    case StmtKind::kVarDecl:
      return ExecTask::Immediate(ExecVarDeclImpl(stmt, ctx, arena));
    default:
      return ExecTask::Immediate(StmtResult::kDone);
  }
}

}  // namespace delta
