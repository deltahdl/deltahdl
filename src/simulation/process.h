#pragma once

#include <coroutine>
#include <cstdint>
#include <exception>

#include "common/types.h"

namespace delta {

// --- Coroutine return type for simulation processes ---

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

// --- Process handle alias ---

using ProcessHandle = std::coroutine_handle<SimCoroutine::promise_type>;

// --- Process kinds matching SystemVerilog constructs ---

enum class ProcessKind : uint8_t {
  kInitial,
  kAlways,
  kAlwaysComb,
  kAlwaysLatch,
  kAlwaysFF,
  kFinal,
  kContAssign,
};

// --- Process: a schedulable simulation process ---

struct Process {
  ProcessKind kind = ProcessKind::kInitial;
  ProcessHandle coro = nullptr;
  Region home_region = Region::kActive;
  uint32_t id = 0;
  bool active = true;

  bool Done() const { return !coro || coro.done(); }

  void Resume() {
    if (coro && !coro.done()) {
      coro.resume();
    }
  }
};

}  // namespace delta
