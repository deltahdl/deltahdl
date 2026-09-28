#include "simulator/lowerer_always_comb.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/awaiters.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

// §9.2.2.2: a variable passed to an output formal of a called task/function is
// written by the call, not read. It must stay out of an always_comb's implicit
// sensitivity list; otherwise the block re-triggers on its own write and spins
// in a zero-delay loop. An inout actual is read as well as written, so only
// pure outputs are excluded. Callee formals come from the runtime subroutine
// registry, which is populated (RegisterModuleSubroutines) before processes are
// lowered.
// Records the base identifiers of any output actuals of a single call node.
static void CollectOutputActualsOfCall(const Expr* call, SimContext& ctx,
                                       std::unordered_set<std::string>& out) {
  const ModuleItem* fn = ctx.FindFunction(call->callee);
  if (!fn) return;
  size_t n = std::min(call->args.size(), fn->func_args.size());
  for (size_t i = 0; i < n; ++i) {
    if (fn->func_args[i].direction != Direction::kOutput) continue;
    const Expr* a = call->args[i];
    while (a && a->kind == ExprKind::kSelect && a->base) a = a->base;
    if (a && a->kind == ExprKind::kIdentifier && !a->text.empty())
      out.insert(std::string(a->text));
  }
}

static void CollectCallOutputActuals(const Expr* expr, SimContext& ctx,
                                     std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    CollectOutputActualsOfCall(expr, ctx, out);
  CollectCallOutputActuals(expr->lhs, ctx, out);
  CollectCallOutputActuals(expr->rhs, ctx, out);
  CollectCallOutputActuals(expr->condition, ctx, out);
  CollectCallOutputActuals(expr->true_expr, ctx, out);
  CollectCallOutputActuals(expr->false_expr, ctx, out);
  CollectCallOutputActuals(expr->base, ctx, out);
  CollectCallOutputActuals(expr->index, ctx, out);
  for (auto* arg : expr->args) CollectCallOutputActuals(arg, ctx, out);
  for (auto* elem : expr->elements) CollectCallOutputActuals(elem, ctx, out);
}

static void CollectCallOutputActuals(const Stmt* stmt, SimContext& ctx,
                                     std::unordered_set<std::string>& out) {
  if (!stmt) return;
  CollectCallOutputActuals(stmt->condition, ctx, out);
  CollectCallOutputActuals(stmt->rhs, ctx, out);
  CollectCallOutputActuals(stmt->expr, ctx, out);
  CollectCallOutputActuals(stmt->for_cond, ctx, out);
  CollectCallOutputActuals(stmt->assert_expr, ctx, out);
  for (auto* s : stmt->stmts) CollectCallOutputActuals(s, ctx, out);
  CollectCallOutputActuals(stmt->then_branch, ctx, out);
  CollectCallOutputActuals(stmt->else_branch, ctx, out);
  CollectCallOutputActuals(stmt->for_body, ctx, out);
  for (auto* fi : stmt->for_inits) CollectCallOutputActuals(fi, ctx, out);
  for (auto* fs : stmt->for_steps) CollectCallOutputActuals(fs, ctx, out);
  CollectCallOutputActuals(stmt->body, ctx, out);
  for (auto* s : stmt->fork_stmts) CollectCallOutputActuals(s, ctx, out);
  for (const auto& ci : stmt->case_items)
    CollectCallOutputActuals(ci.body, ctx, out);
}

// The names of the elements of `info`'s unpacked dimensions from `d` on, each
// `prefix` followed by one index per dimension, as the lowerer names the
// element Variables: `a[0][2]`, counted from each dimension's lower address.
static void AppendElementNames(const ArrayInfo& info, size_t d,
                               const std::string& prefix, Arena& arena,
                               std::vector<std::string_view>& out) {
  bool single = info.dim_sizes.empty();
  if (d == (single ? 1 : info.dim_sizes.size())) {
    out.emplace_back(arena.AllocString(prefix.data(), prefix.size()),
                     prefix.size());
    return;
  }
  uint32_t lo = single ? info.lo : info.dim_los[d];
  uint32_t size = single ? info.size : info.dim_sizes[d];
  for (uint32_t i = 0; i < size; ++i) {
    AppendElementNames(info, d + 1, prefix + "[" + std::to_string(lo + i) + "]",
                       arena, out);
  }
}

std::vector<std::string_view> UnpackedElementNames(std::string_view name,
                                                   SimContext& ctx) {
  std::vector<std::string_view> names;
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue) return names;
  AppendElementNames(*info, 0, std::string(name), ctx.GetArena(), names);
  return names;
}

const std::vector<EventExpr>& ImplicitListEvents(
    const std::vector<EventExpr>& sens, SimContext& ctx, Arena& arena) {
  auto* events = arena.Create<std::vector<EventExpr>>(sens);
  // A constant select, `a[2]`, is on the list already beside its array.
  std::unordered_set<std::string_view> listed;
  for (const auto& ev : sens) {
    if (ev.signal != nullptr) listed.insert(ev.signal->text);
  }
  for (const auto& ev : sens) {
    if (ev.edge != Edge::kNone || ev.signal == nullptr ||
        ev.signal->kind != ExprKind::kIdentifier)
      continue;
    for (std::string_view name : UnpackedElementNames(ev.signal->text, ctx)) {
      if (!listed.insert(name).second) continue;
      auto* element = arena.Create<Expr>();
      element->kind = ExprKind::kIdentifier;
      element->text = name;
      events->push_back({Edge::kNone, element});
    }
  }
  return *events;
}

std::vector<std::string_view> AlwaysCombWatchedNames(
    const Stmt* body, const std::vector<EventExpr>& sens, SimContext& ctx) {
  std::unordered_set<std::string> call_outputs;
  CollectCallOutputActuals(body, ctx, call_outputs);
  std::vector<std::string_view> read_vars;
  read_vars.reserve(sens.size());
  for (const auto& ev : sens) {
    if (!ev.signal || ev.signal->text.empty()) continue;
    if (call_outputs.count(std::string(ev.signal->text)) != 0) continue;
    // §9.2.2.2.1: `y = x + h.a` reads the handle `h` and a member of the object
    // it refers to, and neither is on the list: a write to `h.a` through the
    // handle does not re-run the block.
    if (!ctx.GetVariableClassType(ev.signal->text).empty()) continue;
    read_vars.push_back(ev.signal->text);
    std::vector<std::string_view> elements =
        UnpackedElementNames(ev.signal->text, ctx);
    read_vars.insert(read_vars.end(), elements.begin(), elements.end());
  }
  // A constant select, `a[2]`, is on the list already beside its array.
  std::ranges::sort(read_vars);
  read_vars.erase(std::ranges::unique(read_vars).begin(), read_vars.end());
  DropUnwatchableNames(ctx, read_vars);
  return read_vars;
}

}  // namespace delta
