#include "simulator/static_aggregate.h"

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_scope_stack.h"
#include "simulator/sim_context_types.h"

namespace delta {

static std::string KeptName(std::string_view frame, std::string_view name,
                            SimContext& ctx) {
  std::string key = "$static:";
  if (const Process* proc = ctx.CurrentProcess()) key += proc->inst_prefix;
  key += frame;
  key += '.';
  key += name;
  return key;
}

template <typename Use>
static void WithTopFrameOff(SimContext& ctx, Use use) {
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  if (!stack.empty()) use(stack.back());
  ctx.SwapScopeStack(std::move(stack));
}

template <typename Intern>
static void KeepQueue(Scope& top, std::string_view name,
                      std::string_view kept_name, SimContext& ctx,
                      Intern intern) {
  auto it = top.queues.find(name);
  if (it == top.queues.end()) return;
  QueueObject* kept = ctx.FindQueue(kept_name);
  if (kept == nullptr) kept = ctx.CreateQueue(intern(), 32, -1, true);
  if (kept != it->second) *kept = *it->second;
  it->second = kept;
}

template <typename Intern>
static void KeepAssocArray(Scope& top, std::string_view name,
                           std::string_view kept_name, SimContext& ctx,
                           Intern intern) {
  auto it = top.assoc_arrays.find(name);
  if (it == top.assoc_arrays.end()) return;
  AssocArrayObject* kept = ctx.FindAssocArray(kept_name);
  if (kept == nullptr) kept = ctx.CreateAssocArray(intern(), 32, false);
  if (kept != it->second) *kept = *it->second;
  it->second = kept;
}

template <typename Intern>
static void KeepShape(Scope& top, std::string_view name,
                      std::string_view kept_name, SimContext& ctx,
                      Intern intern) {
  auto it = top.arrays.find(name);
  if (it == top.arrays.end()) return;
  ArrayInfo* kept = ctx.FindArrayInfo(kept_name);
  if (kept == nullptr) {
    ctx.RegisterArray(intern(), *it->second);
    kept = ctx.FindArrayInfo(kept_name);
  } else if (kept != it->second) {
    *kept = *it->second;
  }
  it->second = kept;
}

void RetainStaticAggregate(std::string_view frame, std::string_view name,
                           SimContext& ctx, Arena& arena) {
  std::string kept_name = KeptName(frame, name, ctx);
  auto intern = [&]() -> std::string_view {
    return *arena.Create<std::string>(kept_name);
  };
  WithTopFrameOff(ctx, [&](Scope& top) {
    KeepQueue(top, name, kept_name, ctx, intern);
    KeepAssocArray(top, name, kept_name, ctx, intern);
    KeepShape(top, name, kept_name, ctx, intern);
  });
}

bool RestoreStaticAggregate(std::string_view frame, std::string_view name,
                            SimContext& ctx) {
  std::string kept_name = KeptName(frame, name, ctx);
  bool kept_any = false;
  WithTopFrameOff(ctx, [&](Scope& top) {
    if (QueueObject* kept = ctx.FindQueue(kept_name)) {
      top.queues[name] = kept;
      kept_any = true;
    }
    if (AssocArrayObject* kept = ctx.FindAssocArray(kept_name)) {
      top.assoc_arrays[name] = kept;
      kept_any = true;
    }
    if (ArrayInfo* kept = ctx.FindArrayInfo(kept_name)) {
      top.arrays[name] = kept;
      kept_any = true;
    }
  });
  return kept_any;
}

bool IsEffectivelyStaticLocal(const Stmt* stmt, std::string_view func_name,
                              SimContext& ctx) {
  if (stmt->var_is_static) return true;
  if (stmt->var_is_automatic || func_name.empty()) return false;
  auto* f = ctx.FindFunction(func_name);
  return f && f->is_static && !f->is_automatic;
}

bool IsAutomaticLocal(const Stmt& stmt, SimContext& ctx) {
  if (stmt.var_is_automatic) return true;
  std::string_view func_name = ctx.CurrentFuncName();
  if (stmt.var_is_static || func_name.empty()) return false;
  if (ctx.CurrentMethodClass() != nullptr) return true;
  const ModuleItem* f = ctx.FindFunction(func_name);
  return f != nullptr && f->is_automatic;
}

static bool BlockKeepsDecl(const Stmt& s, SimContext& ctx) {
  if (s.kind != StmtKind::kVarDecl || IsAutomaticLocal(s, ctx)) return false;
  std::string_view func_name = ctx.CurrentFuncName();
  if (IsEffectivelyStaticLocal(&s, func_name, ctx)) return false;
  return func_name.empty() || ctx.FindFunction(func_name) != nullptr;
}

template <typename Use>
static void ForEachBlockStaticName(const Stmt& block, std::string_view frame,
                                   SimContext& ctx, Use use) {
  std::string_view key;
  auto each = [&](const std::vector<Stmt*>& items) {
    for (const Stmt* s : items) {
      if (s == nullptr || !BlockKeepsDecl(*s, ctx)) continue;
      if (key.empty()) key = ctx.StaticFrameKey(frame);
      use(key, s->var_name);
    }
  };
  each(block.stmts);
  each(block.fork_stmts);
}

void RetainBlockAggregates(const Stmt& block, std::string_view frame,
                           SimContext& ctx, Arena& arena) {
  ForEachBlockStaticName(block, frame, ctx,
                         [&](std::string_view key, std::string_view name) {
                           RetainStaticAggregate(key, name, ctx, arena);
                         });
}

void RestoreBlockAggregates(const Stmt& block, std::string_view frame,
                            SimContext& ctx) {
  ForEachBlockStaticName(block, frame, ctx,
                         [&](std::string_view key, std::string_view name) {
                           RestoreStaticAggregate(key, name, ctx);
                         });
}

}  // namespace delta
