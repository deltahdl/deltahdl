#pragma once

#include <coroutine>

#include "simulation/stmt_result.h"

namespace delta {

// Lazy coroutine task for statement execution. Supports suspension via
// co_await (for delays, event controls) with symmetric transfer for
// efficient continuation chaining.
struct ExecTask {
  struct promise_type {
    StmtResult result = StmtResult::kDone;
    std::coroutine_handle<> continuation;

    ExecTask get_return_object() {
      return ExecTask{std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }

    // Symmetric transfer to continuation (parent coroutine).
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

  // Immediate result — no coroutine frame allocated.
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

  // Awaitable interface for co_await.
  bool await_ready() const noexcept { return is_immediate_; }

  std::coroutine_handle<> await_suspend(
      std::coroutine_handle<> caller) noexcept {
    handle_.promise().continuation = caller;
    return handle_;  // Symmetric transfer to child.
  }

  StmtResult await_resume() const noexcept {
    if (is_immediate_) return immediate_result_;
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

}  // namespace delta
