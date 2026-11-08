#include <algorithm>
#include <coroutine>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/disable_scope.h"
#include "simulator/eval_function_hier.h"
#include "simulator/exec_task.h"
#include "simulator/procedural_assertion.h"
#include "simulator/process.h"
#include "simulator/process_termination.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

static bool FlushDeferredQueueOfOutermostScope(std::string_view target,
                                               const Process* current,
                                               SimContext& ctx) {
  const auto& procs = ctx.FindOutermostScopeProcesses(target);
  for (auto* proc : procs) {
    FlushProceduralAssertionQueue(*proc);
    if (proc == current) continue;
    proc->deferred_report_generation++;
  }
  return !procs.empty();
}

static std::string_view DisableTargetLabel(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kMemberAccess &&
         !e->is_scope_resolution) {
    e = e->rhs;
  }
  return e != nullptr && e->kind == ExprKind::kIdentifier ? e->text
                                                          : std::string_view{};
}

static bool TryUnwindForDisable(Process* proc, std::string_view target,
                                SimContext& ctx) {
  const auto& scopes = proc->saved_named_scopes;
  if (std::find(scopes.begin(), scopes.end(), target) == scopes.end()) {
    return false;
  }
  ParkSlot& park = proc->park;
  if (!park.frame || !park.gate || !park.frame.promise().continuation) {
    return false;
  }
  park.gate->open = false;
  auto frame = park.frame;
  park.frame = {};
  park.gate.reset();
  frame.promise().result = StmtResult::kDisable;
  std::coroutine_handle<> cont = frame.promise().continuation;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [proc, cont, target, &ctx]() {
    if (!proc->active) return;
    ctx.SetCurrentProcess(proc);
    ctx.SetDisableTarget(target);
    cont.resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  return true;
}

static std::vector<std::string> DisabledDefinitionInstances(const Expr* e,
                                                            SimContext& ctx) {
  std::vector<std::string> instances;
  if (e->kind != ExprKind::kMemberAccess) return instances;
  const auto kDefinedIn = [&instances, &ctx](std::string_view key) {
    const GenBlockSubroutineScope* scope = ctx.FindGenBlockSubroutineScope(key);
    if (scope != nullptr) instances.push_back(scope->inst_prefix);
    return scope != nullptr;
  };
  const std::string kPath = EvaluatedHierarchicalPath(e, ctx, ctx.GetArena());
  const std::string kLocal = ctx.ActiveInstancePrefix() + kPath;
  if (!kDefinedIn(kLocal)) kDefinedIn(kPath);
  if (!instances.empty()) return instances;
  const std::vector<std::string_view>* definitions =
      ctx.FindForkjoinTask(kLocal);
  if (definitions == nullptr) definitions = ctx.FindForkjoinTask(kPath);
  if (definitions != nullptr) {
    for (std::string_view definition : *definitions) kDefinedIn(definition);
  }
  return instances;
}

StmtResult ExecDisableImpl(const Stmt* stmt, SimContext& ctx) {
  auto target = DisableTargetLabel(stmt->expr);
  if (target.empty()) return StmtResult::kDone;

  auto* current = ctx.CurrentProcess();

  auto procs = ctx.FindNamedScopeProcesses(target);
  std::sort(procs.begin(), procs.end());
  procs.erase(std::unique(procs.begin(), procs.end()), procs.end());
  const std::vector<std::string> kInstances =
      DisabledDefinitionInstances(stmt->expr, ctx);
  if (!kInstances.empty()) {
    std::erase_if(procs, [&kInstances](const Process* proc) {
      return std::ranges::find(kInstances, proc->inst_prefix) ==
             kInstances.end();
    });
  } else {
    procs = ProcessesInDisabledScope(stmt->expr, procs, ctx);
  }
  bool self_disable = false;

  for (auto* proc : procs) {
    if (proc == current) {
      self_disable = true;
      continue;
    }
    if (TryUnwindForDisable(proc, target, ctx)) continue;

    TerminateProcess(*proc, ctx);
    proc->deferred_report_generation++;
  }

  bool named_a_procedure_scope =
      FlushDeferredQueueOfOutermostScope(target, current, ctx);
  GetGlobalVpiContext().NoteDisabled(stmt, ctx.ActiveInstancePrefix());

  if (self_disable) {
    ctx.SetDisableTarget(target);
    return StmtResult::kDisable;
  }

  if (procs.empty() && !named_a_procedure_scope && current) {
    current->cancelled_deferred_labels.insert(std::string(target));
    DisableProceduralAssertion(*current, target);
  }

  return StmtResult::kDone;
}

static void DisableDescendants(Process* proc, SimContext& ctx) {
  for (auto* child : proc->children) {
    TerminateProcess(*child, ctx);
    DisableDescendants(child, ctx);
  }
}

StmtResult ExecDisableForkImpl(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) return StmtResult::kDone;
  DisableDescendants(proc, ctx);
  proc->children.clear();
  return StmtResult::kDone;
}

}  // namespace delta
