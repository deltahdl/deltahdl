#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

// §12.5 of IEEE 1800-2023: the case statement, its casez, casex and case
// inside forms, the unique, unique0 and priority qualifiers of §12.5.3, and
// the matching of each item against the case expression. Split out of
// stmt_exec_control.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at.

namespace delta {

static bool BitIsZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  bool a = (v.words[wi].aval >> bi) & 1;
  bool b = (v.words[wi].bval >> bi) & 1;
  return !a && b;  // z = (aval=0, bval=1)
}

static bool BitIsXZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  return (v.words[wi].bval >> bi) & 1;
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

static bool CaseInsideValueMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  if (!sel.IsKnown()) return false;
  uint32_t nw = (sel.nwords > pat.nwords) ? sel.nwords : pat.nwords;
  for (uint32_t i = 0; i < nw; ++i) {
    uint64_t sa = (i < sel.nwords) ? sel.words[i].aval : 0;
    uint64_t pa = (i < pat.nwords) ? pat.words[i].aval : 0;
    uint64_t pb = (i < pat.nwords) ? pat.words[i].bval : 0;

    if ((sa ^ pa) & ~pb) return false;
  }
  return true;
}

// §12.5.4: in a case-inside statement the case_expression is compared against
// each case_item range element with the set-membership `inside` operator, the
// case_expression being the left operand and each element the right operand. A
// case_item matches when that comparison returns 1'b1; a 1'b0 or 1'bx result is
// no match. The comparison is delegated to the shared inside-operator machinery
// (§11.4.6, §11.4.13) so ranges, tolerances, open bounds, and asymmetric
// wildcard matching all behave identically to the expression-level operator —
// including a selector whose only unknown bits fall on positions the item
// wildcards out, which still matches.
static bool CaseInsidePatternMatch(const Logic4Vec& sel, const Expr* pat,
                                   SimContext& ctx, Arena& arena) {
  return EvalInsideElement(sel, pat, ctx, arena) == 1;
}

// §12.5: a plain `case` comparison succeeds only when every bit matches
// exactly with respect to 0/1/x/z. To make that bitwise comparison meaningful,
// the selector and the item expression are first made equal in length to the
// longer of the two. The bits added by that extension are sign-filled only when
// both operands are signed; if either is unsigned the whole comparison is
// unsigned, so the added bits are zero. This mirrors the width/sign resolution
// the simulator already applies to the equality operators (see 11.6.1, 11.8.1).
// The (aval, bval) bit pair of `v` at position `i`, extending past the
// operand's own width with either its replicated sign bit or zero.
static void CaseBitAt(const Logic4Vec& v, uint32_t i, bool sign_ext,
                      uint64_t& a, uint64_t& b) {
  uint32_t src = i;
  if (i >= v.width) {
    if (!sign_ext || v.width == 0) {
      a = 0;
      b = 0;
      return;
    }
    src = v.width - 1;
  }
  uint32_t wi = src / 64;
  uint32_t bi = src % 64;
  a = (wi < v.nwords) ? ((v.words[wi].aval >> bi) & 1) : 0;
  b = (wi < v.nwords) ? ((v.words[wi].bval >> bi) & 1) : 0;
}

static bool CaseExactMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  uint32_t width = (sel.width > pat.width) ? sel.width : pat.width;
  bool sign_ext = sel.is_signed && pat.is_signed;
  for (uint32_t i = 0; i < width; ++i) {
    uint64_t sa = 0;
    uint64_t sb = 0;
    uint64_t pa = 0;
    uint64_t pb = 0;
    CaseBitAt(sel, i, sign_ext, sa, sb);
    CaseBitAt(pat, i, sign_ext, pa, pb);
    if (sa != pa || sb != pb) return false;
  }
  return true;
}

static bool CaseMatchesMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                             TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseInsideValueMatch(sel, pat);
}

// §12.5 (printed page 321): the case expression and every case item are
// sized to the longest of them, so an item that is an unbased unsized literal
// (§5.7.1) sets every bit of the selector's width -- `'1` against an 8-bit
// selector is ff -- where the bitwise extension below would zero-fill its one
// bit. The item's own width stands where it is not the literal's.
static Logic4Vec CaseItemValue(const Expr* pat, const Logic4Vec& sel,
                               SimContext& ctx, Arena& arena) {
  Logic4Vec pv = EvalExpr(pat, ctx, arena);
  if (pv.fills_width && pv.width < sel.width)
    return FillUnbasedUnsized(pv, sel.width, arena);
  return pv;
}

static bool CaseMatchesPatternMatch(const Logic4Vec& sel, const Expr* pat_expr,
                                    SimContext& ctx, Arena& arena,
                                    TokenKind case_kind) {
  if (pat_expr->kind == ExprKind::kBinary &&
      pat_expr->op == TokenKind::kAmpAmpAmp) {
    auto pat_val = CaseItemValue(pat_expr->lhs, sel, ctx, arena);
    if (!CaseMatchesMatch(sel, pat_val, case_kind)) return false;
    auto guard = EvalExpr(pat_expr->rhs, ctx, arena);
    return guard.IsTruthy();
  }
  auto pv = CaseItemValue(pat_expr, sel, ctx, arena);
  return CaseMatchesMatch(sel, pv, case_kind);
}

static bool CaseItemMatches(const Logic4Vec& sel, const Logic4Vec& pat,
                            TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseExactMatch(sel, pat);
}

static bool CasePatternMatch(const Logic4Vec& sel, const Expr* pat,
                             const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->case_inside) return CaseInsidePatternMatch(sel, pat, ctx, arena);
  if (stmt->case_matches)
    return CaseMatchesPatternMatch(sel, pat, ctx, arena, stmt->case_kind);
  return CaseItemMatches(sel, CaseItemValue(pat, sel, ctx, arena),
                         stmt->case_kind);
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

// §12.5.3.1: the item a unique or unique0 case selects, the violations the
// qualifier defines reported on the way: more than one matching item, and
// for unique no matching item and no default.
static const Stmt* SelectUniqueCaseBody(const Stmt* stmt, const Logic4Vec& sel,
                                        CaseQualifier qual, SimContext& ctx,
                                        Arena& arena) {
  auto info = ScanUniqueCaseItems(sel, stmt, ctx, arena);
  if (info.match_count > 1) {
    ctx.AddPendingViolation(stmt->range.start,
                            "unique case: multiple items matched",
                            Subclause("12.5.3.1"));
  }
  if (info.first_match_body) return info.first_match_body;
  const Stmt* default_body = FindCaseDefault(stmt);
  if (default_body) return default_body;
  if (!info.has_default && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation(stmt->range.start,
                            "unique case: no matching item found",
                            Subclause("12.5.3.1"));
  }
  return nullptr;
}

// §12.5: the item a case selects by the linear search, the first whose
// pattern matches, else the default; §12.5.3.1 reports a priority case
// that selects none.
static const Stmt* SelectStandardCaseBody(const Stmt* stmt,
                                          const Logic4Vec& sel,
                                          CaseQualifier qual, SimContext& ctx,
                                          Arena& arena) {
  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    if (CaseItemHasMatch(sel, item, stmt, ctx, arena)) return item.body;
  }
  const Stmt* default_body = FindCaseDefault(stmt);
  if (default_body) return default_body;
  if (qual == CaseQualifier::kPriority) {
    ctx.AddPendingViolation(stmt->range.start,
                            "priority case: no matching item found",
                            Subclause("12.5.3.1"));
  }
  return nullptr;
}

const Stmt* SelectCaseBody(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto qual = stmt->qualifier;
  auto sel = EvalExpr(stmt->condition, ctx, arena);
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    return SelectUniqueCaseBody(stmt, sel, qual, ctx, arena);
  }
  return SelectStandardCaseBody(stmt, sel, qual, ctx, arena);
}

ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  const Stmt* body = SelectCaseBody(stmt, ctx, arena);
  StmtResult r = StmtResult::kDone;
  if (body != nullptr) r = co_await ExecStmt(body, ctx, arena);
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return r;
}

}  // namespace delta
