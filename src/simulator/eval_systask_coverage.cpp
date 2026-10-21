// IEEE 1800-2023 §40.3.2 "Built-in coverage access system functions":
// $coverage_control, $coverage_get_max, $coverage_get, $coverage_merge and
// $coverage_save, evaluated against the run's coverage-control state.

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

// Builds the integer result of the §40.3.2 coverage functions, which is one of
// the §40.3.1 status values or a positive count. §40.3.2.2 and §40.3.2.3 give
// `SV_COV_OVERFLOW (-2) and `SV_COV_ERROR (-1) as negative results, so the
// value is a signed 32-bit integer, as an int would be: an unsigned one
// printed -1 as 4294967295 and was never below zero.
static Logic4Vec CoverageIntResult(Arena& arena, int value) {
  Logic4Vec result = MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(value));
  result.is_signed = true;
  return result;
}

// §40.3.2.1 Table 40-2: the scope_def argument beside the scope says how far
// the call reaches - `SV_COV_HIER over the instance and everything below it,
// `SV_COV_MODULE over that instance alone, leaving out the instances below it.
// The two are the §40.3.1 constants 11 and 10; nothing else names a scope
// definition, and a call that wrote something else wrote a bad argument.
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

// §40.3.2.1, §40.3.2.4 and §40.3.2.5: the string argument at `index` - a
// module definition name, or the name a coverage database is found by. A
// string is a value, so the argument is evaluated and a string variable names
// what it holds. A missing argument is the empty string, which names nothing.
static std::string CoverageStrArg(const Expr* expr, size_t index,
                                  SimContext& ctx, Arena& arena) {
  if (expr->args.size() <= index || expr->args[index] == nullptr) return {};
  const Expr* arg = expr->args[index];
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
  return EvalStringArg(arg, ctx, arena);
}

// §40.3.2.1 Table 40-2: the instance a hierarchical path names, as the
// coverage state knows it, or the empty string where the path names none. A
// path headed by `$root.` is read from the top of the design; any other is read
// from the calling scope and then from each scope above it, as §23.8 resolves a
// name upward, and last as a path from the top, so an instance of the current
// scope is named without a dot, as the table's note allows.
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

// §40.3.2.1 Table 40-2: the scope the modules_or_instance argument at `index`
// names, in the terms the coverage-control state keys its scopes by. `$root`
// alone is the root of the design. A hierarchical path is the instance it
// names; a name that is no instance is read as a value, since a string
// variable is named the same way. Anything else is a string, a module
// definition name or the path of an instance.
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

// §40.3.2.1: $coverage_control(control_constant, coverage_type, scope_def,
// modules_or_instance) performs the control action named by its first argument
// over the scope named by its fourth and returns one of the §40.3.1 status
// values. The action is applied to the simulation's coverage-control state.
static Logic4Vec EvalCoverageControl(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {
  auto status_vec = [&arena](CoverageStatus status) {
    return CoverageIntResult(arena, static_cast<int>(status));
  };
  // A control constant outside the §40.3.1 set (or a missing one) is a bad
  // argument, reported as `SV_COV_ERROR.
  if (expr->args.empty()) return status_vec(CoverageStatus::kError);
  int control_value =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  CoverageControl control{};
  if (!CoverageControlFromInt(control_value, &control)) {
    return status_vec(CoverageStatus::kError);
  }
  // §40.3.2.1 Table 40-2: the third argument says whether the hierarchy below
  // the named scope is controlled with it. A scope definition the clause does
  // not name is a bad argument, which is the `SV_COV_ERROR the clause has any
  // operation report, usually for an argument in error.
  bool include_below = true;
  if (!CoverageScopeDefIncludesBelow(expr, ctx, arena, 2, &include_below)) {
    return status_vec(CoverageStatus::kError);
  }
  // The second argument is the coverage type the action is on, present once
  // the third is, and the fourth names the module definition or instance.
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  return status_vec(ctx.GetCoverageControlState().Control(
      control, coverage_type, CoverageScopeArg(expr, 3, ctx, arena),
      include_below));
}

// Shared evaluator for the §40.3.2 coverage query functions. They all return
// the §40.3.2.2 integer result pattern: `SV_COV_ERROR when the first
// (coverage_type) argument is missing, otherwise the value produced by `query`
// from the coverage type and the optional string argument (scope/name) at
// `str_arg_index`.
enum class CoverageQuery : std::uint8_t { kGetMax, kGet, kMerge, kSave };
static Logic4Vec EvalCoverageQuery(const Expr* expr, SimContext& ctx,
                                   Arena& arena, CoverageQuery query,
                                   size_t str_arg_index) {
  // The first argument selects the coverage type; without it the arguments are
  // incorrect, reported as `SV_COV_ERROR.
  if (expr->args.empty()) {
    return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
  }
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  // §40.3.2.1 Table 40-2 governs the two hierarchy queries too: their second
  // argument is the same scope_def, and their third the same scope. The
  // database queries of §40.3.2.4/.5 name no scope, so they have none to read
  // and none to refuse, and their string is the database's name.
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

// §40.3.2.2: $coverage_get_max(coverage_type, scope_def, modules_or_instance)
// returns the value representing 100% coverage for the given coverage type over
// the named hierarchy — the sum of all coverable items of that type. The value
// is a property of the design and stays constant for the whole simulation. The
// integer result is one of the §40.3.1 status values (`SV_COV_ERROR for bad
// arguments, `SV_COV_NOCOV when no coverage is available, `SV_COV_OVERFLOW when
// the count is too large to represent) or a positive maximum coverage number.
// The third argument names the module definition or instance, as the scope is
// specified per $coverage_control() (§40.3.2.1).
static Logic4Vec EvalCoverageGetMax(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kGetMax,
                           /*str_arg_index=*/2);
}

// §40.3.2.3: $coverage_get(coverage_type, scope_def, modules_or_instance)
// returns the current coverage value for the given coverage type over the named
// hierarchy — the number of coverable items of that type covered so far. It
// follows the same return pattern as $coverage_get_max() (§40.3.2.2), but the
// positive value is the current coverage level rather than the maximum, so
// coverage% is coverage_get()/coverage_get_max() * 100. The integer result is
// one of the §40.3.1 status values (`SV_COV_ERROR for bad arguments,
// `SV_COV_NOCOV when no coverage is available, `SV_COV_OVERFLOW when the count
// is too large to represent) or a positive current coverage number.
static Logic4Vec EvalCoverageGet(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kGet,
                           /*str_arg_index=*/2);
}

// §40.3.2.4: $coverage_merge(coverage_type, "name") loads and merges coverage
// data of the given coverage type from the named coverage database into the
// simulation. `name` is an arbitrary, implementation-specific locator for the
// database. The integer result is one of the §40.3.1 status values:
// `SV_COV_OK when the data are found (for this design) and merged,
// `SV_COV_NOCOV when the data are found but do not contain the requested
// coverage type, and `SV_COV_ERROR when the name does not exist, the data are
// from a different design, or another error occurs. A missing name locates no
// database, which is the error case.
static Logic4Vec EvalCoverageMerge(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kMerge,
                           /*str_arg_index=*/1);
}

// §40.3.2.5: $coverage_save(coverage_type, "name") saves the current coverage
// of the given type to the tool's coverage database under `name`, so a later
// $coverage_merge() (§40.3.2.4) with the same name can load it. Saving never
// affects the coverage state of this simulation. The integer result is one of
// the §40.3.1 status values: `SV_COV_OK when the data are saved, `SV_COV_NOCOV
// when no such coverage is available in this design (nothing is saved), and
// `SV_COV_ERROR when an error occurs during the save — in which case the entry
// for `name` is removed to preserve coverage-database integrity. A missing
// name leaves the destination empty.
static Logic4Vec EvalCoverageSave(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kSave,
                           /*str_arg_index=*/1);
}

// §40.3.2: the coverage query/control system functions. Returns the result
// when `name` is in the $coverage_* family, or nullopt otherwise.
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
