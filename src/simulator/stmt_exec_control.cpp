#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"

namespace delta {

// Tears down the static and named scope a named begin/end block pushed on
// entry. A no-op for unnamed blocks. Always called immediately before
// ExecBlock returns so the scope stack is balanced on every exit path.
static void TeardownNamedBlockScope(const Stmt* stmt, SimContext& ctx,
                                    bool named) {
  if (!named) return;
  ctx.PopActiveNamedScope();
  ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  ctx.PopStaticScope(stmt->label);
}

ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool named = !stmt->label.empty();
  if (named) {
    ctx.PushStaticScope(stmt->label);
    ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
    ctx.PushActiveNamedScope(stmt->label);
  }
  for (auto* s : stmt->stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kDisable) {
      if (named && ctx.GetDisableTarget() == stmt->label) {
        ctx.ClearDisableTarget();
        TeardownNamedBlockScope(stmt, ctx, named);
        co_return StmtResult::kDone;
      }
      TeardownNamedBlockScope(stmt, ctx, named);
      co_return StmtResult::kDisable;
    }
    if (result != StmtResult::kDone) {
      TeardownNamedBlockScope(stmt, ctx, named);
      co_return result;
    }
    if (ctx.StopRequested()) {
      TeardownNamedBlockScope(stmt, ctx, named);
      co_return StmtResult::kDone;
    }

    if (auto* cur = ctx.CurrentProcess(); cur && !cur->active) {
      TeardownNamedBlockScope(stmt, ctx, named);
      co_return StmtResult::kDone;
    }
  }
  TeardownNamedBlockScope(stmt, ctx, named);
  co_return StmtResult::kDone;
}

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

ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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
static bool CaseExactMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  uint32_t width = (sel.width > pat.width) ? sel.width : pat.width;
  bool sign_ext = sel.is_signed && pat.is_signed;
  // Returns the (aval,bval) bit pair of `v` at position `i`, extending past the
  // operand's own width with either its replicated sign bit or zero.
  auto bit_at = [sign_ext](const Logic4Vec& v, uint32_t i, uint64_t& a,
                           uint64_t& b) {
    uint32_t src = i;
    if (i >= v.width) {
      if (!(sign_ext && v.width > 0)) {
        a = 0;
        b = 0;
        return;
      }
      src = v.width - 1;
    }
    uint32_t wi = src / 64, bi = src % 64;
    a = (wi < v.nwords) ? ((v.words[wi].aval >> bi) & 1) : 0;
    b = (wi < v.nwords) ? ((v.words[wi].bval >> bi) & 1) : 0;
  };
  for (uint32_t i = 0; i < width; ++i) {
    uint64_t sa, sb, pa, pb;
    bit_at(sel, i, sa, sb);
    bit_at(pat, i, pa, pb);
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

static bool CaseMatchesPatternMatch(const Logic4Vec& sel, const Expr* pat_expr,
                                    SimContext& ctx, Arena& arena,
                                    TokenKind case_kind) {
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

ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto qual = stmt->qualifier;
  auto sel = EvalExpr(stmt->condition, ctx, arena);

  StmtResult r{};
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = co_await ExecUniqueCase(stmt, sel, qual, ctx, arena);
  } else {
    r = co_await ExecStandardCase(stmt, sel, qual, ctx, arena);
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return r;
}

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

// Pops the dynamic scope a typed for-init introduced and the static scope a
// label introduced, in the order ExecFor pushed them. Called on every ExecFor
// exit path to keep the scope stack balanced.
// §9.3.5: a statement label on a foreach loop, or a for loop that declares its
// loop variable, names the implicit begin-end block the loop creates. Pushing
// the static scope alone (for hierarchical name resolution) is not enough for a
// `disable <label>` to find the loop; registering the label as a named scope of
// the running process — exactly as ExecBlock does for a named begin-end block —
// lets the disable resolve so the loop can consume it. Paired 1:1 with
// ExitLoopLabelScope so the scope stack stays balanced on every exit path.
static void EnterLoopLabelScope(const Stmt* stmt, SimContext& ctx,
                                bool labeled) {
  if (!labeled) return;
  ctx.PushStaticScope(stmt->label);
  ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
}

static void ExitLoopLabelScope(const Stmt* stmt, SimContext& ctx,
                               bool labeled) {
  if (!labeled) return;
  ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  ctx.PopStaticScope(stmt->label);
}

static void TeardownForScopes(const Stmt* stmt, SimContext& ctx, bool scoped,
                              bool labeled) {
  if (scoped) ctx.PopScope();
  ExitLoopLabelScope(stmt, ctx, labeled);
}

// How a loop should react to the StmtResult returned by its body, factored out
// of the repeated "break / propagate / keep looping" branch shared by every
// loop executor in this file. kPropagate means the caller must unwind its
// scopes and co_return the body's result unchanged.
enum class LoopAction : std::uint8_t { kKeepLooping, kBreakLoop, kPropagate };

static LoopAction ClassifyLoopBodyResult(StmtResult result) {
  if (result == StmtResult::kBreak) return LoopAction::kBreakLoop;
  if (result != StmtResult::kDone && result != StmtResult::kContinue) {
    return LoopAction::kPropagate;
  }
  return LoopAction::kKeepLooping;
}

// §9.3.5: a statement label on a foreach loop, or on a for loop that declares
// its loop variable, names the implicit begin-end block the loop creates. Per
// §9.6.2, disabling a named block terminates it and resumes execution at the
// following statement. So when the loop body bubbles up a kDisable that targets
// the loop's own label, the disable is consumed here and turned into a normal
// loop exit rather than propagating further up the process. Returns true when
// the loop should stop.
static bool LoopDisableTargetsOwnLabel(const Stmt* stmt, StmtResult result,
                                       bool labeled, SimContext& ctx) {
  if (result != StmtResult::kDisable || !labeled) return false;
  if (ctx.GetDisableTarget() != stmt->label) return false;
  ctx.ClearDisableTarget();
  return true;
}

// Evaluates a for-loop's optional continuation condition. A loop with no
// condition runs unconditionally; otherwise it continues only while the
// condition is truthy.
static bool ForConditionHolds(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->for_cond) return true;
  auto cond = EvalExpr(stmt->for_cond, ctx, arena);
  return cond.IsTruthy();
}

ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  EnterLoopLabelScope(stmt, ctx, labeled);
  bool scoped = HasTypedForInit(stmt);
  if (scoped) ctx.PushScope();
  CreateForInitVars(stmt, ctx);
  for (auto* init : stmt->for_inits) co_await ExecStmt(init, ctx, arena);
  while (!ctx.StopRequested()) {
    if (!ForConditionHolds(stmt, ctx, arena)) break;
    auto result = co_await ExecStmt(stmt->for_body, ctx, arena);
    auto action = ClassifyLoopBodyResult(result);
    if (action == LoopAction::kBreakLoop) break;
    if (action == LoopAction::kPropagate) {
      if (LoopDisableTargetsOwnLabel(stmt, result, labeled, ctx)) break;
      TeardownForScopes(stmt, ctx, scoped, labeled);
      co_return result;
    }
    for (auto* step : stmt->for_steps) co_await ExecStmt(step, ctx, arena);
  }
  TeardownForScopes(stmt, ctx, scoped, labeled);
  co_return StmtResult::kDone;
}

ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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

ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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

// §12.7.2: derive how many times a repeat-loop body runs from the count
// expression, already evaluated once before the loop begins. An unknown or
// high-impedance value, or a negative value of a signed expression, yields no
// iterations.
static uint64_t RepeatIterationCount(const Logic4Vec& count_val) {
  if (!count_val.IsKnown()) return 0;
  if (count_val.is_signed && count_val.width > 0) {
    uint32_t msb_word = (count_val.width - 1) / 64;
    uint64_t msb_mask = uint64_t{1} << ((count_val.width - 1) % 64);
    if (count_val.words[msb_word].aval & msb_mask) return 0;
  }
  return count_val.ToUint64();
}

ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto count_val = EvalExpr(stmt->condition, ctx, arena);
  uint64_t count = RepeatIterationCount(count_val);
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

ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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
  // §12.7.3: a string is treated as a dynamic array of bytes, so the loop runs
  // once per character. The value packs eight bits per character, so the
  // character count is the bit width divided by eight.
  if (ctx.IsStringVariable(name)) return var->value.width / 8;
  return var->value.width;
}

// §12.7.3: foreach is illegal on a wildcard-indexed associative array. Reports
// the diagnostic and returns true when the named array is such a wildcard
// array, signalling that ExecForeach must abandon the loop.
static bool ForeachOnWildcardAssoc(const std::string& arr_name,
                                   SimContext& ctx) {
  if (arr_name.empty()) return false;
  auto* aa = ctx.FindAssocArray(arr_name);
  if (aa && aa->is_wildcard) {
    ctx.GetDiag().Error(
        {},
        "foreach not allowed on wildcard associative array '" + arr_name + "'");
    return true;
  }
  return false;
}

// §12.7.3: maps a zero-based iteration counter to the array's declared index
// value. With array-info present the index walks the declared range, counting
// down for a descending dimension; otherwise it stays zero-based.
static uint32_t ForeachIndexForIteration(const ArrayInfo* info, uint32_t size,
                                         uint32_t i) {
  if (!info) return i;
  return info->is_descending ? (info->lo + size - 1 - i) : (info->lo + i);
}

// Result of the non-coroutine prologue of ExecForeach: the array name, its
// iteration count, and whether the loop should run at all. `bail` is set when
// the loop must terminate immediately (wildcard associative array, or a
// zero-length iteration domain) without entering the body.
struct ForeachSetup {
  std::string arr_name;
  uint32_t size = 0;
  bool bail = false;
};

// §12.7.3: resolves the array being iterated and how many iterations it
// implies, reporting the wildcard-associative-array error as a side effect.
// Pure prologue computation kept out of the ExecForeach coroutine so the
// coroutine body stays small.
static ForeachSetup ComputeForeachSetup(const Stmt* stmt, SimContext& ctx) {
  ForeachSetup setup;
  setup.arr_name = GetForeachArrayName(stmt->expr);
  if (ForeachOnWildcardAssoc(setup.arr_name, ctx)) {
    setup.bail = true;
    return setup;
  }
  setup.size = GetArraySize(stmt, ctx);
  if (setup.size == 0) setup.bail = true;
  return setup;
}

// Returns the foreach loop-variable name, or an empty view when the iteration
// dimension is unnamed (a `,` placeholder in the index list).
static std::string_view ForeachIterName(const Stmt* stmt) {
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    return stmt->foreach_vars[0];
  }
  return {};
}

// Assigns the loop variable for iteration `i`, mapping the zero-based counter
// onto the array's declared index range. A no-op when the dimension is
// unnamed (`iter_var` is null).
static void SetForeachIterVar(Variable* iter_var, const ArrayInfo* info,
                              uint32_t size, uint32_t i, Arena& arena) {
  if (!iter_var) return;
  uint32_t index = ForeachIndexForIteration(info, size, i);
  iter_var->value = MakeLogic4VecVal(arena, 32, index);
}

// Pops the dynamic scope ExecForeach pushed for the loop body and the static
// scope a label introduced, in the order they were pushed. Called on every
// ExecForeach exit path that runs after the body scope is established.
static void TeardownForeachScopes(const Stmt* stmt, SimContext& ctx,
                                  bool labeled) {
  ctx.PopScope();
  ExitLoopLabelScope(stmt, ctx, labeled);
}

// §12.7.3: for a multidimensional (unpacked) array each loop variable
// corresponds to one dimension. Collects, in declaration order, the loop
// variable name plus its dimension's low index and size for every dimension
// that has a named loop variable, so ExecForeach can iterate them as nested
// loops. A dimension whose variable slot is omitted (an empty name) is not
// iterated and contributes no entry.
struct ForeachDimIter {
  std::string_view name;
  uint32_t lo;
  uint32_t size;
};

static std::vector<ForeachDimIter> CollectForeachDims(const Stmt* stmt,
                                                      const ArrayInfo* info) {
  std::vector<ForeachDimIter> dims;
  size_t ndims = info->dim_sizes.size();
  size_t nvars = stmt->foreach_vars.size();
  for (size_t k = 0; k < nvars && k < ndims; ++k) {
    if (stmt->foreach_vars[k].empty()) continue;
    uint32_t lo = (k < info->dim_los.size()) ? info->dim_los[k] : 0;
    dims.push_back({stmt->foreach_vars[k], lo, info->dim_sizes[k]});
  }
  return dims;
}

// §12.7.3: drives a multidimensional foreach as nested loops. A flat odometer
// over the product of the iterated dimension sizes yields the same nesting the
// LRM prescribes: the last (highest-cardinality, innermost) dimension changes
// most rapidly, the first (lowest-cardinality, outermost) most slowly. Each
// step maps the counter back to per-dimension index values before running the
// body once, so `continue` advances to the next combination and `break` (or a
// disable of the loop's own label) leaves the whole loop.
static ExecTask ExecForeachMultiDim(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena, const ArrayInfo* info,
                                    bool labeled) {
  std::vector<ForeachDimIter> dims = CollectForeachDims(stmt, info);
  ctx.PushScope();
  std::vector<Variable*> vars;
  uint64_t total = 1;
  for (const auto& d : dims) {
    vars.push_back(ctx.CreateLocalVariable(d.name, 32));
    total *= d.size;
  }
  for (uint64_t n = 0; n < total && !ctx.StopRequested(); ++n) {
    uint64_t rem = n;
    for (size_t d = dims.size(); d-- > 0;) {
      uint32_t idx = static_cast<uint32_t>(rem % dims[d].size);
      rem /= dims[d].size;
      if (vars[d]) {
        vars[d]->value = MakeLogic4VecVal(arena, 32, dims[d].lo + idx);
      }
    }
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    auto action = ClassifyLoopBodyResult(result);
    if (action == LoopAction::kBreakLoop) break;
    if (action == LoopAction::kPropagate) {
      if (LoopDisableTargetsOwnLabel(stmt, result, labeled, ctx)) break;
      TeardownForeachScopes(stmt, ctx, labeled);
      co_return result;
    }
  }
  TeardownForeachScopes(stmt, ctx, labeled);
  co_return StmtResult::kDone;
}

ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  EnterLoopLabelScope(stmt, ctx, labeled);
  ForeachSetup setup = ComputeForeachSetup(stmt, ctx);
  if (setup.bail) {
    ExitLoopLabelScope(stmt, ctx, labeled);
    co_return StmtResult::kDone;
  }
  const std::string& arr_name = setup.arr_name;
  uint32_t size = setup.size;

  std::string_view iter_name = ForeachIterName(stmt);

  // §12.7.3: the loop variable steps through the array's declared index range,
  // not a fixed zero base. A descending dimension counts down from its high
  // index. Variables, packed vectors, and strings carry no array-info entry
  // and keep the natural zero-based ordering.
  const ArrayInfo* info =
      arr_name.empty() ? nullptr : ctx.FindArrayInfo(arr_name);

  // §12.7.3: a multidimensional unpacked array binds one loop variable per
  // dimension; iterate every dimension as nested loops rather than only the
  // outermost.
  if (info && info->dim_sizes.size() >= 2 && stmt->foreach_vars.size() >= 2) {
    co_return co_await ExecForeachMultiDim(stmt, ctx, arena, info, labeled);
  }

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size && !ctx.StopRequested(); ++i) {
    SetForeachIterVar(iter_var, info, size, i, arena);
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    auto action = ClassifyLoopBodyResult(result);
    if (action == LoopAction::kBreakLoop) break;
    if (action == LoopAction::kPropagate) {
      if (LoopDisableTargetsOwnLabel(stmt, result, labeled, ctx)) break;
      TeardownForeachScopes(stmt, ctx, labeled);
      co_return result;
    }
  }

  TeardownForeachScopes(stmt, ctx, labeled);
  co_return StmtResult::kDone;
}

ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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

uint64_t DelayTicksFromValue(const Logic4Vec& val) {
  if (!val.IsKnown()) return 0;
  uint64_t raw = val.ToUint64();
  if (val.is_signed && val.width > 0 && val.width < 64) {
    int64_t signed_val = SignExtend(raw, val.width);
    if (signed_val < 0) return static_cast<uint64_t>(signed_val);
  }
  return raw;
}

uint64_t DelayValueToTicks(const Logic4Vec& val, const SimContext& ctx) {
  const TimeScale& scale = ctx.CurrentTimeScale();
  TimeUnit precision = ctx.GlobalPrecision();
  if (val.is_real) {
    // §3.14.1: a real delay is rounded to the nearest multiple of the design
    // element's time precision before it is used. The value carries IEEE-754
    // bits in its low word; recover the double and let RealDelayToTicks apply
    // the precision-step rounding and scale the result to global-precision
    // ticks. A negative delay has no meaning here, so it collapses to no wait.
    double d = 0.0;
    uint64_t bits = val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    if (d < 0.0) return 0;
    return RealDelayToTicks(d, scale, precision);
  }
  // An integer delay has no fractional part to round, but is still scaled from
  // the issuing element's time unit to the global tick base.
  return DelayToTicks(DelayTicksFromValue(val), scale, precision);
}

ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    ticks = DelayValueToTicks(EvalExpr(stmt->delay, ctx, arena), ctx);
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static bool IsNamedEvent(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return false;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return false;
  if (!ev.signal || ev.signal->kind != ExprKind::kIdentifier) return false;
  auto* var = ctx.FindVariable(ev.signal->text);
  return var && var->is_event;
}

static bool HasSequenceEvent(const Stmt* stmt) {
  for (const auto& ev : stmt->events) {
    if (ev.is_sequence_event) return true;
  }
  return false;
}

ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->events.empty()) {
    if (HasSequenceEvent(stmt)) {
      co_await SequenceEventAwaiter{ctx, stmt->events};
    } else if (IsNamedEvent(stmt, ctx)) {
      co_await NamedEventAwaiter{ctx, stmt->events[0].signal->text};
    } else {
      co_await EventAwaiter{ctx, stmt->events, arena};
    }
    // §12.4.2.1: a process that suspended on an event control reaches a
    // violation report flush point when it resumes; any unique/priority
    // reports accumulated before the suspension are discarded.
    ctx.FlushPendingViolations();
    // §16.4.2: that resume is equally a deferred assertion flush point, so
    // deferred reports pending from before the suspend are cleared as well.
    ctx.FlushPendingDeferredReports();
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
