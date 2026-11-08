#include "simulator/dpi_task_call.h"

#include <pthread.h>
#if __has_include(<bits/pthreadtypes.h>)
#include <bits/pthreadtypes.h>
#endif

#include <condition_variable>
#include <cstddef>
#include <mutex>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_function_internal.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"

namespace delta {

namespace {

struct DpiTaskChannel {
  std::mutex mutex;
  std::condition_variable turn_taken;
  bool simulator_turn = false;
  bool finished = false;
  const DpiRtExport* request = nullptr;
  std::string_view request_key;
  std::vector<DpiArgValue>* request_args = nullptr;
  bool disabled = false;
  DpiImportCall* call = nullptr;
};

thread_local DpiTaskChannel* g_channel = nullptr;

constexpr std::size_t kCallStackBytes = std::size_t{256} << 20U;

void PassTurn(DpiTaskChannel& channel, bool to_simulator) {
  std::unique_lock<std::mutex> lock(channel.mutex);
  channel.simulator_turn = to_simulator;
  channel.turn_taken.notify_all();
  channel.turn_taken.wait(lock, [&channel, to_simulator] {
    return channel.simulator_turn != to_simulator;
  });
}

void AwaitSimulatorTurn(DpiTaskChannel& channel) {
  std::unique_lock<std::mutex> lock(channel.mutex);
  channel.turn_taken.wait(lock, [&channel] { return channel.simulator_turn; });
}

void* RunImportCall(void* raw) {
  auto* channel = static_cast<DpiTaskChannel*>(raw);
  g_channel = channel;
  CallDpiImport(*channel->call);
  g_channel = nullptr;
  std::lock_guard<std::mutex> lock(channel->mutex);
  channel->finished = true;
  channel->simulator_turn = true;
  channel->turn_taken.notify_all();
  return nullptr;
}

bool StartImportCall(DpiTaskChannel& channel, pthread_t& thread) {
  pthread_attr_t attr;
  if (pthread_attr_init(&attr) != 0) return false;
  pthread_attr_setstacksize(&attr, kCallStackBytes);
  const bool kStarted =
      pthread_create(&thread, &attr, &RunImportCall, &channel) == 0;
  pthread_attr_destroy(&attr);
  return kStarted;
}

std::string_view KeyFromRunningInstance(std::string_view key, SimContext& ctx) {
  const std::string kPrefix = ctx.ActiveInstancePrefix();
  if (!kPrefix.empty() && key.starts_with(kPrefix)) {
    key.remove_prefix(kPrefix.size());
  }
  return key;
}

ExecTask RunRequestedTask(DpiTaskChannel& channel, SimContext& ctx,
                          Arena& arena) {
  const DpiRtExport& exp = *channel.request;
  std::vector<DpiArgValue>& args = *channel.request_args;
  Expr* call = DpiExportCall(channel.request_key, exp, args, ctx);
  call->callee =
      *arena.Create<std::string>(KeyFromRunningInstance(call->callee, ctx));
  auto* enable = arena.Create<Stmt>();
  enable->kind = StmtKind::kExprStmt;
  enable->expr = call;
  StmtResult result = co_await ExecStmt(enable, ctx, arena);
  if (result != StmtResult::kDisable)
    ReadDpiExportOutputs(call, exp, args, ctx);
  co_return result;
}

}  // namespace

bool EnablesDpiImportTask(const Expr* expr, SimContext& ctx) {
  DpiRuntime* dpi = ctx.GetDpiRuntime();
  if (dpi == nullptr || expr->callee.empty()) return false;
  const DpiRtFunction* import =
      dpi->FindImportIn(ctx.ActiveUnitScope(), expr->callee);
  return import != nullptr && import->is_task;
}

ExecTask ExecDpiImportTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  DpiImportCall call;
  if (!BeginDpiImportCall(expr, ctx, arena, call)) co_return StmtResult::kDone;
  DpiTaskChannel channel;
  channel.call = &call;
  pthread_t thread{};
  if (!StartImportCall(channel, thread)) {
    CallDpiImport(call);
    FinishDpiImportCall(call, ctx, arena);
    co_return StmtResult::kDone;
  }
  bool disabled = false;
  AwaitSimulatorTurn(channel);
  while (!channel.finished) {
    StmtResult result = co_await RunRequestedTask(channel, ctx, arena);
    channel.disabled = result == StmtResult::kDisable;
    disabled = disabled || channel.disabled;
    PassTurn(channel, false);
  }
  pthread_join(thread, nullptr);
  FinishDpiImportCall(call, ctx, arena);
  co_return disabled ? StmtResult::kDisable : StmtResult::kDone;
}

DpiArgValue RunExportedTaskFromC(const DpiRtExport& exp, std::string_view key,
                                 std::vector<DpiArgValue>& args) {
  DpiTaskChannel* channel = g_channel;
  if (channel == nullptr) return DpiArgValue::FromInt(0);
  channel->request = &exp;
  channel->request_key = key;
  channel->request_args = &args;
  PassTurn(*channel, true);
  if (channel->disabled) DpiSetCurrentDisabledState(true);
  return DpiArgValue::FromInt(0);
}

}  // namespace delta
