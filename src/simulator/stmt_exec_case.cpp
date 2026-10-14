#include <algorithm>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/exec_task.h"
#include "simulator/pattern_match.h"
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

// §12.5.1: a z bit, which casez ignores, and an x or z bit, which casex
// ignores, as the (aval, bval) pair CaseBitAt gives.
static bool BitIsZ(uint64_t a, uint64_t b) { return a == 0 && b == 1; }

static bool BitIsXZ(uint64_t /*a*/, uint64_t b) { return b == 1; }

using BitPredicate = bool (*)(uint64_t, uint64_t);

// §12.5.1 keeps §12.5's lengths and signedness: the two operands are extended
// to the longer length, by sign where both are signed (CaseBitAt), and a bit
// the predicate keeps compares as the plain case compares it, both halves, so
// a casez x matches an x alone.
static bool CaseDontCareMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                              BitPredicate skip_bit) {
  uint32_t width = (sel.width > pat.width) ? sel.width : pat.width;
  bool sign_ext = sel.is_signed && pat.is_signed;
  for (uint32_t i = 0; i < width; ++i) {
    uint64_t sa = 0;
    uint64_t sb = 0;
    uint64_t pa = 0;
    uint64_t pb = 0;
    CaseBitAt(sel, i, sign_ext, sa, sb);
    CaseBitAt(pat, i, sign_ext, pa, pb);
    if (skip_bit(sa, sb) || skip_bit(pa, pb)) continue;
    if (sa != pa || sb != pb) return false;
  }
  return true;
}

static bool CasexMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsXZ);
}

static bool CasezMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsZ);
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

// §12.6.1: wherever pattern matching compares two bits, casez ignores z bits
// and casex x and z bits; written with case, it ignores none, so a constant
// pattern is compared as a plain case item is (§12.5).
static bool CaseMatchesMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                             TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseExactMatch(sel, pat);
}

// §12.6.1: a constant pattern of a pattern-matching case compared with what it
// is matched against, sized as CaseItemValue sizes a plain item's value, by
// the statement's case kind.
static bool CaseMatchesValueMatch(const Logic4Vec& value,
                                  const Logic4Vec& constant,
                                  TokenKind case_kind, Arena& arena) {
  if (constant.fills_width && constant.width < value.width)
    return CaseMatchesMatch(
        value, FillUnbasedUnsized(constant, value.width, arena), case_kind);
  return CaseMatchesMatch(value, constant, case_kind);
}

// The case expression as each item is matched against it: its value, and, for
// a pattern-matching case (§12.6.1), what the patterns are matched against and
// the identifiers the first item to match bound, which its statement reads.
struct CaseSubject {
  Logic4Vec sel;
  PatternSubject pattern;
  std::optional<std::vector<PatternBinding>> bound;
  // §12.5 (printed page 321): for a plain case, casez or casex, the length
  // every expression of the statement is evaluated at, the longest of the case
  // expression's and the items', and whether all of them are signed, which
  // alone makes the extension to that length a sign extension.
  uint32_t width = 0;
  bool all_signed = false;
};

// Sizes the plain case, casez or casex `stmt` as §12.5 sizes it.
static void SizeCaseStatement(const Stmt* stmt, SimContext& ctx,
                              CaseSubject& cs) {
  cs.width = SimSelfWidth(stmt->condition, ctx);
  cs.all_signed = SimSelfSigned(stmt->condition, ctx);
  for (const auto& item : stmt->case_items) {
    for (const Expr* pat : item.patterns) {
      cs.width = std::max(cs.width, SimSelfWidth(pat, ctx));
      cs.all_signed = cs.all_signed && SimSelfSigned(pat, ctx);
    }
  }
}

// An expression of a plain case, casez or casex statement evaluated at the
// statement's length and extended to it, by sign only where every expression
// is signed. An unbased unsized literal (§5.7.1) sets every bit of that
// length. A real or string operand is compared as it stands.
static Logic4Vec CaseOperandValue(const Expr* e, const CaseSubject& cs,
                                  SimContext& ctx, Arena& arena) {
  Logic4Vec v = EvalExpr(e, ctx, arena, cs.width);
  if (v.is_real || v.is_string) return v;
  if (v.fills_width && v.width < cs.width)
    return FillUnbasedUnsized(v, cs.width, arena);
  // Where every expression's type is signed, as far as their forms show it,
  // each comparison extends its pair by sign, a form SimSelfSigned does not
  // read -- a select, a call -- answering by its value's own (CaseBitAt).
  if (cs.all_signed) return v;
  v.is_signed = false;
  return v.width < cs.width ? ExtendVec(v, cs.width, false, arena) : v;
}

// §12.6.1: the `&&&` filters of the item pattern `e` after its pattern
// `pattern`, evaluated from the left and each true where it is nonzero.
static bool FiltersHold(const Expr* e, const Expr* pattern, SimContext& ctx,
                        Arena& arena) {
  if (e == pattern) return true;
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kAmpAmpAmp) {
    return FiltersHold(e->lhs, pattern, ctx, arena) &&
           EvalExpr(e->rhs, ctx, arena).IsTruthy();
  }
  return EvalExpr(e, ctx, arena).IsTruthy();
}

// §12.6.1: an item's pattern, the leftmost operand of the `&&&` filters it may
// carry, matched against the case expression (MatchPattern). The filters read
// the identifiers the pattern binds, so those are created in a scope of their
// own while the filters run; the first matching item's are kept in `cs` for
// its statement.
static bool CaseMatchesPatternMatch(CaseSubject& cs, const Expr* pat_expr,
                                    SimContext& ctx, Arena& arena,
                                    TokenKind case_kind) {
  const Expr* pattern = pat_expr;
  while (pattern->kind == ExprKind::kBinary &&
         pattern->op == TokenKind::kAmpAmpAmp) {
    pattern = pattern->lhs;
  }
  std::vector<PatternBinding> bindings;
  PatternMatchEnv env{case_kind, CaseMatchesValueMatch, ctx, arena, bindings};
  if (!MatchPattern(pattern, cs.pattern, env)) return false;
  bool scoped = !bindings.empty() && pattern != pat_expr;
  if (scoped) {
    ctx.PushScope();
    InstallPatternBindings(bindings, ctx);
  }
  bool holds = FiltersHold(pat_expr, pattern, ctx, arena);
  if (scoped) ctx.PopScope();
  if (holds && !cs.bound) cs.bound = std::move(bindings);
  return holds;
}

static bool CaseItemMatches(const Logic4Vec& sel, const Logic4Vec& pat,
                            TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseExactMatch(sel, pat);
}

static bool CasePatternMatch(CaseSubject& cs, const Expr* pat, const Stmt* stmt,
                             SimContext& ctx, Arena& arena) {
  if (stmt->case_inside) return CaseInsidePatternMatch(cs.sel, pat, ctx, arena);
  if (stmt->case_matches)
    return CaseMatchesPatternMatch(cs, pat, ctx, arena, stmt->case_kind);
  return CaseItemMatches(cs.sel, CaseOperandValue(pat, cs, ctx, arena),
                         stmt->case_kind);
}

static bool CaseItemHasMatch(CaseSubject& cs, const CaseItem& item,
                             const Stmt* stmt, SimContext& ctx, Arena& arena) {
  for (auto* pat : item.patterns) {
    if (CasePatternMatch(cs, pat, stmt, ctx, arena)) return true;
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

static UniqueCaseResult ScanUniqueCaseItems(CaseSubject& cs, const Stmt* stmt,
                                            SimContext& ctx, Arena& arena) {
  UniqueCaseResult result;
  for (const auto& item : stmt->case_items) {
    if (item.is_default) {
      result.has_default = true;
      continue;
    }
    if (CaseItemHasMatch(cs, item, stmt, ctx, arena)) {
      result.match_count++;
      if (!result.first_match_body) result.first_match_body = item.body;
    }
  }
  return result;
}

// §12.5.3.1: the item a unique or unique0 case selects, the violations the
// qualifier defines reported on the way: more than one matching item, and
// for unique no matching item and no default.
static const Stmt* SelectUniqueCaseBody(const Stmt* stmt, CaseSubject& cs,
                                        CaseQualifier qual, SimContext& ctx,
                                        Arena& arena) {
  auto info = ScanUniqueCaseItems(cs, stmt, ctx, arena);
  if (info.match_count > 1) {
    ctx.AddPendingViolation(stmt->range.start,
                            "unique case: multiple items matched",
                            Subclause("12.5.3.1"), qual);
  }
  if (info.first_match_body) return info.first_match_body;
  const Stmt* default_body = FindCaseDefault(stmt);
  if (default_body) return default_body;
  if (!info.has_default && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation(stmt->range.start,
                            "unique case: no matching item found",
                            Subclause("12.5.3.1"), qual);
  }
  return nullptr;
}

// §12.5: the item a case selects by the linear search, the first whose
// pattern matches, else the default; §12.5.3.1 reports a priority case
// that selects none.
static const Stmt* SelectStandardCaseBody(const Stmt* stmt, CaseSubject& cs,
                                          CaseQualifier qual, SimContext& ctx,
                                          Arena& arena) {
  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    if (CaseItemHasMatch(cs, item, stmt, ctx, arena)) return item.body;
  }
  const Stmt* default_body = FindCaseDefault(stmt);
  if (default_body) return default_body;
  if (qual == CaseQualifier::kPriority) {
    ctx.AddPendingViolation(stmt->range.start,
                            "priority case: no matching item found",
                            Subclause("12.5.3.1"), qual);
  }
  return nullptr;
}

CaseSelection SelectCaseItem(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto qual = stmt->qualifier;
  CaseSubject cs;
  if (stmt->case_matches) {
    cs.pattern = PatternSubjectOf(stmt->condition, ctx, arena);
    cs.sel = cs.pattern.value;
  } else if (stmt->case_inside) {
    cs.sel = EvalExpr(stmt->condition, ctx, arena);
  } else {
    SizeCaseStatement(stmt, ctx, cs);
    cs.sel = CaseOperandValue(stmt->condition, cs, ctx, arena);
  }
  CaseSelection chosen;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    chosen.body = SelectUniqueCaseBody(stmt, cs, qual, ctx, arena);
  } else {
    chosen.body = SelectStandardCaseBody(stmt, cs, qual, ctx, arena);
  }
  if (cs.bound) chosen.bindings = std::move(*cs.bound);
  return chosen;
}

ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(ctx.StmtFrameName(stmt));
  CaseSelection chosen = SelectCaseItem(stmt, ctx, arena);
  StmtResult r = StmtResult::kDone;
  if (chosen.body != nullptr) {
    // §12.6.1: the identifiers the item's pattern bound are in scope in its
    // statement.
    bool scoped = !chosen.bindings.empty();
    if (scoped) {
      ctx.PushScope();
      InstallPatternBindings(chosen.bindings, ctx);
    }
    r = co_await ExecStmt(chosen.body, ctx, arena);
    if (scoped) ctx.PopScope();
  }
  if (labeled) ctx.PopStaticScope(ctx.StmtFrameName(stmt));
  co_return r;
}

}  // namespace delta
