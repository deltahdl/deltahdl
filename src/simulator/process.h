#pragma once

#include <coroutine>
#include <cstdint>
#include <exception>
#include <functional>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/exec_task.h"
#include "simulator/scope.h"

namespace delta {

struct SimCoroutine {
  struct promise_type {
    SimCoroutine get_return_object() {
      auto h = std::coroutine_handle<promise_type>::from_promise(*this);
      return SimCoroutine{h};
    }

    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() { exception = std::current_exception(); }

    std::exception_ptr exception = nullptr;
  };

  using HandleType = std::coroutine_handle<promise_type>;

  explicit SimCoroutine(HandleType h) : handle(h) {}

  SimCoroutine(const SimCoroutine&) = delete;
  SimCoroutine& operator=(const SimCoroutine&) = delete;

  SimCoroutine(SimCoroutine&& other) noexcept : handle(other.handle) {
    other.handle = nullptr;
  }

  SimCoroutine& operator=(SimCoroutine&& other) noexcept {
    if (this != &other) {
      Destroy();
      handle = other.handle;
      other.handle = nullptr;
    }
    return *this;
  }

  ~SimCoroutine() { Destroy(); }

  bool Done() const { return !handle || handle.done(); }

  void Resume() {
    if (handle && !handle.done()) {
      handle.resume();
    }
  }

  HandleType Release() noexcept {
    auto h = handle;
    handle = nullptr;
    return h;
  }

  HandleType handle = nullptr;

 private:
  void Destroy() {
    if (handle) {
      handle.destroy();
      handle = nullptr;
    }
  }
};

using ProcessHandle = std::coroutine_handle<SimCoroutine::promise_type>;

enum class ProcessKind : uint8_t {
  kInitial,
  kAlways,
  kAlwaysComb,
  kAlwaysLatch,
  kAlwaysFF,
  kFinal,
  kContAssign,
};

enum class ProcessState : uint8_t {
  kFinished = 0,
  kRunning = 1,
  kWaiting = 2,
  kSuspended = 3,
  kKilled = 4,
};

struct WaitForkState {
  uint32_t remaining = 0;
  std::coroutine_handle<> waiter;
};

struct ClassObject;
struct ClassTypeInfo;
struct ProceduralAssertionState;
struct ProceduralCheckerAssertion;
struct PropertyTreeState;
struct SequencePropertyState;

struct Process {
  ProcessKind kind = ProcessKind::kInitial;
  ProcessHandle coro = nullptr;
  Region home_region = Region::kActive;
  uint32_t id = 0;
  bool active = true;
  bool is_reactive = false;
  const void* waiting_on_sync = nullptr;
  std::vector<const void*> waiting_on_events;

  uint32_t program_block_id = 0;

  bool is_concurrent_clocked = false;

  std::vector<EventExpr> gclk_future_event;
  const Stmt* future_gclk_attempt_of = nullptr;
  const Stmt* origin = nullptr;

  WaitForkState wait_fork_state;

  std::vector<Process*> children;

  ProcessState sv_state = ProcessState::kRunning;
  bool is_suspended = false;
  std::coroutine_handle<> pending_wake;
  ParkSlot park;
  bool start_deferred = false;
  std::vector<std::coroutine_handle<>> await_waiters;
  std::function<void()> fork_release;

  uint32_t rng_seed = 0;

  std::mt19937 rng;
  bool rng_initialized = false;

  struct PendingViolation {
    SourceLoc loc;
    std::string msg;
    std::string_view subclause;
    uint32_t type_bit = 0;
    std::string scope;
  };
  std::vector<PendingViolation> pending_violations;

  uint64_t deferred_report_generation = 0;

  std::unordered_set<std::string> cancelled_deferred_labels;

  struct QueuedDeferredReports {
    uint64_t latest = 0;
    uint64_t flushed_through = 0;
  };
  uint64_t deferred_reports_queued = 0;
  std::unordered_map<const Stmt*, QueuedDeferredReports>
      queued_deferred_reports;

  std::unordered_map<const Stmt*, SequencePropertyState*>
      sequence_property_states;
  std::unordered_map<const Stmt*, PropertyTreeState*> property_tree_states;
  EventExpr woken_by;
  std::unordered_map<const Stmt*, ProceduralAssertionState*>
      procedural_assertions;
  std::unordered_map<const Stmt*,
                     std::vector<const ProceduralCheckerAssertion*>>
      checker_instance_assertions;
  bool expect_decided = false;
  bool expect_holds = false;

  std::string inst_prefix;

  std::vector<std::string> gen_prefixes;
  std::string gen_block_name;

  std::vector<Scope> saved_scope_stack;
  std::vector<std::string_view> saved_named_scopes;
  std::vector<ClassObject*> saved_this_stack;
  std::vector<const ClassTypeInfo*> saved_method_class_stack;
  std::vector<std::string> caller_inst_prefixes;
  std::vector<std::vector<std::string>> caller_gen_prefixes;
  std::vector<FrameOwnerEntry> frame_owners;
  bool stand_in = false;
  bool is_static_init = false;
  std::vector<std::string_view> spawned_in_named_scopes;

  ~Process() {
    if (coro) coro.destroy();
  }

  Process() = default;
  Process(const Process&) = delete;
  Process& operator=(const Process&) = delete;

  bool Done() const { return !coro || coro.done(); }

  void Finish() {
    if (sv_state == ProcessState::kKilled) return;
    sv_state = ProcessState::kFinished;
    auto waiters = std::move(await_waiters);
    await_waiters.clear();
    for (auto& w : waiters) {
      if (w) w.resume();
    }
  }

  void Kill() {
    active = false;
    sv_state = ProcessState::kKilled;
    auto waiters = std::move(await_waiters);
    await_waiters.clear();
    for (auto& w : waiters) w.resume();
  }

  void ReleaseFromFork() {
    auto release = std::move(fork_release);
    fork_release = nullptr;
    if (release) release();
  }

  void Resume() {
    if (!active || !coro || coro.done()) return;
    if (is_suspended) {
      start_deferred = true;
      return;
    }
    coro.resume();
  }
};

}  // namespace delta
