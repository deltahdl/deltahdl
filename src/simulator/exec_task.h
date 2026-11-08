#pragma once

#include <coroutine>
#include <memory>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

#include "simulator/stmt_result.h"

namespace delta {

struct ExecTask {
  struct promise_type {
    StmtResult result = StmtResult::kDone;
    std::coroutine_handle<> continuation;

    ExecTask& await_transform(ExecTask& task) noexcept { return task; }
    ExecTask&& await_transform(ExecTask&& task) noexcept {
      return std::move(task);
    }
    template <typename A>
    auto await_transform(A&& awaiter) noexcept;

    ExecTask get_return_object() {
      return ExecTask{std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }

    auto final_suspend() noexcept {
      struct Transfer {
        std::coroutine_handle<> cont;
        bool await_ready() noexcept { return false; }
        std::coroutine_handle<> await_suspend(
            std::coroutine_handle<>) noexcept {
          return cont ? cont : std::noop_coroutine();
        }
        void await_resume() noexcept {}
      };
      return Transfer{continuation};
    }

    void return_value(StmtResult r) { result = r; }
    void unhandled_exception() {}
  };

  using Handle = std::coroutine_handle<promise_type>;

  explicit ExecTask(Handle h) : handle_(h) {}

  static ExecTask Immediate(StmtResult r) {
    ExecTask t{nullptr};
    t.immediate_result_ = r;
    t.is_immediate_ = true;
    return t;
  }

  ExecTask(const ExecTask&) = delete;
  ExecTask& operator=(const ExecTask&) = delete;

  ExecTask(ExecTask&& o) noexcept
      : handle_(o.handle_),
        immediate_result_(o.immediate_result_),
        is_immediate_(o.is_immediate_) {
    o.handle_ = nullptr;
  }

  ExecTask& operator=(ExecTask&& o) noexcept {
    if (this != &o) {
      Destroy();
      handle_ = o.handle_;
      immediate_result_ = o.immediate_result_;
      is_immediate_ = o.is_immediate_;
      o.handle_ = nullptr;
    }
    return *this;
  }

  ~ExecTask() { Destroy(); }

  bool await_ready() const noexcept { return is_immediate_; }

  std::coroutine_handle<> await_suspend(
      std::coroutine_handle<> caller) noexcept {
    handle_.promise().continuation = caller;
    return handle_;
  }

  StmtResult await_resume() const noexcept {
    if (is_immediate_) return immediate_result_;
    return handle_.promise().result;
  }

  StmtResult RunToCompletion() noexcept {
    handle_.resume();
    return handle_.promise().result;
  }

 private:
  void Destroy() {
    if (handle_) {
      handle_.destroy();
      handle_ = nullptr;
    }
  }

  Handle handle_ = nullptr;
  StmtResult immediate_result_ = StmtResult::kDone;
  bool is_immediate_ = false;
};

struct WakeGate {
  bool open = true;
};

struct WakeRelay {
  struct promise_type {
    WakeRelay get_return_object() noexcept {
      return WakeRelay{
          std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_never final_suspend() noexcept { return {}; }
    void return_void() noexcept {}
    void unhandled_exception() noexcept {}
  };
  std::coroutine_handle<promise_type> handle;
};

inline WakeRelay RelayWake(std::coroutine_handle<> target,
                           std::shared_ptr<WakeGate> gate) {
  std::shared_ptr<WakeGate> held = std::move(gate);
  if (held->open) {
    held->open = false;
    target.resume();
  }
  co_return;
}

struct ParkSlot {
  std::coroutine_handle<ExecTask::promise_type> frame;
  std::shared_ptr<WakeGate> gate;
  const std::vector<std::string_view>* named_scopes = nullptr;
};

inline thread_local ParkSlot* g_park_slot = nullptr;

template <typename A>
struct ParkedAwait {
  A inner;
  std::coroutine_handle<ExecTask::promise_type> frame;
  ParkSlot* slot = nullptr;

  bool await_ready() { return inner.await_ready(); }

  template <typename P>
  auto await_suspend(std::coroutine_handle<P> h) {
    using Result = decltype(inner.await_suspend(h));
    ParkSlot* running = g_park_slot;
    if (running == nullptr || running->named_scopes == nullptr ||
        running->named_scopes->empty()) {
      return inner.await_suspend(h);
    }
    auto gate = std::make_shared<WakeGate>();
    WakeRelay relay = RelayWake(h, gate);
    slot = running;
    slot->frame = frame;
    slot->gate = gate;
    if constexpr (std::is_same_v<Result, bool>) {
      if (!inner.await_suspend(relay.handle)) {
        relay.handle.destroy();
        Unpark();
        return false;
      }
      return true;
    } else {
      return inner.await_suspend(relay.handle);
    }
  }

  decltype(auto) await_resume() {
    Unpark();
    return inner.await_resume();
  }

 private:
  void Unpark() {
    if (slot != nullptr && slot->frame == frame) {
      slot->frame = {};
      slot->gate.reset();
    }
    slot = nullptr;
  }
};

template <typename A>
auto ExecTask::promise_type::await_transform(A&& awaiter) noexcept {
  return ParkedAwait<A>{
      std::forward<A>(awaiter),
      std::coroutine_handle<promise_type>::from_promise(*this)};
}

}  // namespace delta
