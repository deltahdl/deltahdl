#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/coverage_control.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"

namespace delta {

static Logic4Vec CoverageIntResult(Arena& arena, int value) {
  Logic4Vec result = MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(value));
  result.is_signed = true;
  return result;
}

constexpr int kSvCovModule = 10;
constexpr int kSvCovHier = 11;

static bool CoverageScopeDefIncludesBelow(const Expr* expr, SimContext& ctx,
                                          Arena& arena, size_t index,
                                          bool* include_below) {
  if (expr->args.size() <= index) return false;
  int scope_def =
      static_cast<int>(EvalExpr(expr->args[index], ctx, arena).ToUint64());
  if (scope_def == kSvCovHier) {
    *include_below = true;
    return true;
  }
  if (scope_def == kSvCovModule) {
    *include_below = false;
    return true;
  }
  return false;
}

static std::string CoverageStrArg(const Expr* expr, size_t index,
                                  SimContext& ctx, Arena& arena) {
  if (expr->args.size() <= index || expr->args[index] == nullptr) return {};
  const Expr* arg = expr->args[index];
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
  return EvalStringArg(arg, ctx, arena);
}

static std::string CoverageInstancePath(const Expr* arg, SimContext& ctx) {
  const CoverageControlState& cov = ctx.GetCoverageControlState();
  const Expr* head = arg;
  while (head->kind == ExprKind::kMemberAccess) head = head->lhs;
  std::vector<std::string> names = ScopeItemNames(arg, ScopeHierName(ctx));
  if (head->scope_prefix == kCoverageRootScope) {
    return cov.IsRegistered(names.front()) ? names.front() : std::string();
  }
  for (size_t i = 1; i < names.size(); ++i) {
    if (cov.IsRegistered(names[i])) return names[i];
  }
  return cov.IsRegistered(names.front()) ? names.front() : std::string();
}

static std::string CoverageScopeArg(const Expr* expr, size_t index,
                                    SimContext& ctx, Arena& arena) {
  if (expr->args.size() <= index || expr->args[index] == nullptr) return {};
  const Expr* arg = expr->args[index];
  if (arg->kind == ExprKind::kSystemCall && arg->callee == kCoverageRootScope) {
    return std::string(kCoverageRootScope);
  }
  if (arg->kind == ExprKind::kIdentifier ||
      arg->kind == ExprKind::kMemberAccess) {
    std::string path = CoverageInstancePath(arg, ctx);
    if (!path.empty()) return path;
  }
  return CoverageStrArg(expr, index, ctx, arena);
}

static Logic4Vec EvalCoverageControl(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {
  auto status_vec = [&arena](CoverageStatus status) {
    return CoverageIntResult(arena, static_cast<int>(status));
  };
  if (expr->args.empty()) return status_vec(CoverageStatus::kError);
  int control_value =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  CoverageControl control{};
  if (!CoverageControlFromInt(control_value, &control)) {
    return status_vec(CoverageStatus::kError);
  }
  bool include_below = true;
  if (!CoverageScopeDefIncludesBelow(expr, ctx, arena, 2, &include_below)) {
    return status_vec(CoverageStatus::kError);
  }
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  return status_vec(ctx.GetCoverageControlState().Control(
      control, coverage_type, CoverageScopeArg(expr, 3, ctx, arena),
      include_below));
}

enum class CoverageQuery : std::uint8_t { kGetMax, kGet, kMerge, kSave };
static Logic4Vec EvalCoverageQuery(const Expr* expr, SimContext& ctx,
                                   Arena& arena, CoverageQuery query,
                                   size_t str_arg_index) {
  if (expr->args.empty()) {
    return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
  }
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  bool include_below = true;
  bool queries_a_scope =
      query == CoverageQuery::kGetMax || query == CoverageQuery::kGet;
  std::string str_arg = queries_a_scope
                            ? CoverageScopeArg(expr, str_arg_index, ctx, arena)
                            : CoverageStrArg(expr, str_arg_index, ctx, arena);
  if (queries_a_scope &&
      !CoverageScopeDefIncludesBelow(expr, ctx, arena, 1, &include_below)) {
    return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
  }
  auto& state = ctx.GetCoverageControlState();
  switch (query) {
    case CoverageQuery::kGetMax:
      return CoverageIntResult(
          arena, state.CoverageMax(str_arg, coverage_type, include_below));
    case CoverageQuery::kGet:
      return CoverageIntResult(
          arena, state.CoverageGet(str_arg, coverage_type, include_below));
    case CoverageQuery::kMerge:
      return CoverageIntResult(
          arena, static_cast<int>(state.CoverageMerge(coverage_type, str_arg)));
    case CoverageQuery::kSave:
      return CoverageIntResult(
          arena, static_cast<int>(state.CoverageSave(coverage_type, str_arg)));
  }
  return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
}

static Logic4Vec EvalCoverageGetMax(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kGetMax, 2);
}

static Logic4Vec EvalCoverageGet(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kGet, 2);
}

static Logic4Vec EvalCoverageMerge(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kMerge, 1);
}

static Logic4Vec EvalCoverageSave(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kSave, 1);
}

std::optional<Logic4Vec> EvalCoverageSysCall(const Expr* expr, SimContext& ctx,
                                             Arena& arena,
                                             std::string_view name) {
  if (name == "$coverage_control") return EvalCoverageControl(expr, ctx, arena);

  if (name == "$coverage_get_max") return EvalCoverageGetMax(expr, ctx, arena);

  if (name == "$coverage_get") return EvalCoverageGet(expr, ctx, arena);

  if (name == "$coverage_merge") return EvalCoverageMerge(expr, ctx, arena);

  if (name == "$coverage_save") return EvalCoverageSave(expr, ctx, arena);

  return std::nullopt;
}

}  // namespace delta
