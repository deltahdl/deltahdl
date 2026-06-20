#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"

namespace delta {

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
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
        co_return StmtResult::kDone;
      }
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return StmtResult::kDisable;
    }
    if (result != StmtResult::kDone) {
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return result;
    }
    if (ctx.StopRequested()) {
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return StmtResult::kDone;
    }

    if (auto* cur = ctx.CurrentProcess(); cur && !cur->active) {
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return StmtResult::kDone;
    }
  }
  if (named) {
    ctx.PopActiveNamedScope();
    ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
    ctx.PopStaticScope(stmt->label);
  }
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
  return a && b;
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

static bool CaseInsideRangeMatch(const Logic4Vec& sel, const Expr* pat,
                                 SimContext& ctx, Arena& arena) {
  if (!sel.IsKnown()) return false;
  uint64_t sv = sel.ToUint64();

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
    if (lo > hi) {
      uint64_t t = lo;
      lo = hi;
      hi = t;
    }
    return sv >= lo && sv <= hi;
  }

  auto is_dollar = [](const Expr* e) {
    return e->kind == ExprKind::kIdentifier && e->text == "$";
  };
  uint64_t lo =
      is_dollar(pat->index) ? 0 : EvalExpr(pat->index, ctx, arena).ToUint64();
  uint64_t hi =
      is_dollar(pat->index_end)
          ? ((sel.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << sel.width) - 1)
          : EvalExpr(pat->index_end, ctx, arena).ToUint64();
  if (lo > hi) {
    uint64_t t = lo;
    lo = hi;
    hi = t;
  }
  return sv >= lo && sv <= hi;
}

static bool CaseInsidePatternMatch(const Logic4Vec& sel, const Expr* pat,
                                   SimContext& ctx, Arena& arena) {
  if (pat->kind == ExprKind::kSelect && pat->index && pat->index_end)
    return CaseInsideRangeMatch(sel, pat, ctx, arena);
  auto pat_val = EvalExpr(pat, ctx, arena);
  return CaseInsideValueMatch(sel, pat_val);
}

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

  StmtResult r;
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

ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  bool scoped = HasTypedForInit(stmt);
  if (scoped) ctx.PushScope();
  CreateForInitVars(stmt, ctx);
  for (auto* init : stmt->for_inits) co_await ExecStmt(init, ctx, arena);
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
    for (auto* step : stmt->for_steps) co_await ExecStmt(step, ctx, arena);
  }
  if (scoped) ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
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

ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::string arr_name = GetForeachArrayName(stmt->expr);
  if (!arr_name.empty()) {
    auto* aa = ctx.FindAssocArray(arr_name);
    if (aa && aa->is_wildcard) {
      ctx.GetDiag().Error(
          {}, "foreach not allowed on wildcard associative array '" + arr_name +
                  "'");
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
  }
  uint32_t size = GetArraySize(stmt, ctx);
  if (size == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  // §12.7.3: the loop variable steps through the array's declared index range,
  // not a fixed zero base. A descending dimension counts down from its high
  // index. Variables, packed vectors, and strings carry no array-info entry
  // and keep the natural zero-based ordering.
  const ArrayInfo* info =
      arr_name.empty() ? nullptr : ctx.FindArrayInfo(arr_name);

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size && !ctx.StopRequested(); ++i) {
    if (iter_var) {
      uint32_t index = i;
      if (info) {
        index =
            info->is_descending ? (info->lo + size - 1 - i) : (info->lo + i);
      }
      iter_var->value = MakeLogic4VecVal(arena, 32, index);
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

static uint64_t DelayTicksFromValue(const Logic4Vec& val) {
  if (!val.IsKnown()) return 0;
  uint64_t raw = val.ToUint64();
  if (val.is_signed && val.width > 0 && val.width < 64) {
    int64_t signed_val = SignExtend(raw, val.width);
    if (signed_val < 0) return static_cast<uint64_t>(signed_val);
  }
  return raw;
}

ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    ticks = DelayTicksFromValue(EvalExpr(stmt->delay, ctx, arena));
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
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
