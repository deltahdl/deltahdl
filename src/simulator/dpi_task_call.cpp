#include "simulator/dpi_task_call.h"

#include <pthread.h>

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

// What passes between an imported task's C code and the process that enabled
// it: whose turn it is, the exported task the C code asks for and its
// arguments, whether a disable ended that task, and whether the C code has
// returned.
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

// The channel of the imported task whose C code the calling thread runs.
thread_local DpiTaskChannel* g_channel = nullptr;

// The C code may recurse as deeply as the run's own, which runs on a deep
// stack (RunOnDeepStack in src/main.cpp).
constexpr std::size_t kCallStackBytes = std::size_t{256} << 20U;

// Passes the turn to the other thread and waits for it to come back.
void PassTurn(DpiTaskChannel& channel, bool to_simulator) {
  std::unique_lock<std::mutex> lock(channel.mutex);
  channel.simulator_turn = to_simulator;
  channel.turn_taken.notify_all();
  channel.turn_taken.wait(lock, [&channel, to_simulator] {
    return channel.simulator_turn != to_simulator;
  });
}

// Waits for the C code to hand the turn over, with a request or its return.
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

// Starts the C code of `channel`'s call on a thread of its own.
bool StartImportCall(DpiTaskChannel& channel, pthread_t& thread) {
  pthread_attr_t attr;
  if (pthread_attr_init(&attr) != 0) return false;
  pthread_attr_setstacksize(&attr, kCallStackBytes);
  const bool kStarted =
      pthread_create(&thread, &attr, &RunImportCall, &channel) == 0;
  pthread_attr_destroy(&attr);
  return kStarted;
}

// The key of the subroutine keyed `key` from the root of the design, as the
// running instance names it.
std::string_view KeyFromRunningInstance(std::string_view key, SimContext& ctx) {
  const std::string kPrefix = ctx.ActiveInstancePrefix();
  if (!kPrefix.empty() && key.starts_with(kPrefix)) {
    key.remove_prefix(kPrefix.size());
  }
  return key;
}

// §35.8: runs the exported task the C code asked for as a task enable of the
// enabling process, so its timing controls suspend that process.
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
  const DpiRtFunction* import = dpi->FindImport(expr->callee);
  return import != nullptr && import->is_task;
}

ExecTask ExecDpiImportTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  DpiImportCall call;
  if (!BeginDpiImportCall(expr, ctx, arena, call)) co_return StmtResult::kDone;
  DpiTaskChannel channel;
  channel.call = &call;
  pthread_t thread{};
  if (!StartImportCall(channel, thread)) {
    // With no thread to run on, the C code runs here, as a call that consumes
    // no time does.
    CallDpiImport(call);
    FinishDpiImportCall(call, ctx, arena);
    co_return StmtResult::kDone;
  }
  bool disabled = false;
  AwaitSimulatorTurn(channel);
  while (!channel.finished) {
    StmtResult result = co_await RunRequestedTask(channel, ctx, arena);
    // §35.9: a disable that ended the exported task returns 1 from it.
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
  // §35.9: the C code learns of the disable through svIsDisabledState(),
  // which reads the state of its own thread.
  if (channel->disabled) DpiSetCurrentDisabledState(true);
  return DpiArgValue::FromInt(0);
}

}  // namespace delta
