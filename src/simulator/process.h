#pragma once

#include <coroutine>
#include <cstdint>
#include <exception>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

struct Variable;

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

struct Process {
  ProcessKind kind = ProcessKind::kInitial;
  ProcessHandle coro = nullptr;
  Region home_region = Region::kActive;
  uint32_t id = 0;
  bool active = true;
  bool is_reactive = false;

  uint32_t program_block_id = 0;

  WaitForkState wait_fork_state;

  std::vector<Process*> children;

  ProcessState sv_state = ProcessState::kRunning;
  bool is_suspended = false;
  // §9.7: when a process is suspended, a one-shot delay wake that elapses
  // during the suspension cannot simply be dropped -- it holds the only handle
  // to the coroutine's parked continuation (which is nested below
  // Process::coro, so resuming coro would resume the wrong frame). Stash that
  // inner handle here and replay it on resume(). Empty when no elapsed wake is
  // pending.
  std::coroutine_handle<> pending_wake;
  std::vector<std::coroutine_handle<>> await_waiters;

  uint32_t rng_seed = 0;

  // Per §18.14.2 thread stability: each thread carries its own RNG so that
  // draws made from this thread do not depend on the scheduler's interleaving
  // with siblings. The owning SimContext seeds rng on creation, lazily marks
  // rng_initialized true on first use, and may be reset by srandom().
  std::mt19937 rng;
  bool rng_initialized = false;

  std::vector<std::string> pending_violations;

  std::string inst_prefix;

  // §13.3.2: a task may be enabled more than once concurrently, and every
  // variable of an automatic task (and, more generally, every block-scoped
  // local) must be private to each activation. Automatic/block locals live on
  // the context's single scope stack while this process runs; when the process
  // suspends and another runs, its scope stack is parked here and swapped back
  // in on resume by SimContext::SetCurrentProcess, so concurrent activations
  // never see each other's locals. Kept last so adding it does not shift the
  // offsets of the fields above.
  std::vector<std::unordered_map<std::string_view, Variable*>>
      saved_scope_stack;

  ~Process() {
    if (coro) coro.destroy();
  }

  Process() = default;
  Process(const Process&) = delete;
  Process& operator=(const Process&) = delete;

  bool Done() const { return !coro || coro.done(); }

  void Resume() {
    if (active && !is_suspended && coro && !coro.done()) {
      coro.resume();
    }
  }
};

}  // namespace delta
