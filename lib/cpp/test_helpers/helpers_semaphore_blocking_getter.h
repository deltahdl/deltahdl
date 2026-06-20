#pragma once

#include <coroutine>
#include <vector>

#include "simulator/awaiters.h"
#include "simulator/sync_objects.h"

using namespace delta;

// Minimal coroutine used to model a process that blocks in semaphore get().
// It starts suspended; the first resume() runs it up to the co_await, which
// either acquires keys immediately or parks the handle on the semaphore's
// waiter queue. When put() returns enough keys, WakeWaiters() resumes it and
// the body records its id, so a sequence of resumes reveals the order in which
// blocked processes were served.
struct BlockingGetter {
  struct promise_type {
    BlockingGetter get_return_object() {
      return BlockingGetter{
          std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
  std::coroutine_handle<promise_type> h;
};

inline BlockingGetter SpawnGetter(delta::SemaphoreObject& sem, int count,
                                  std::vector<int>& ran, int id) {
  co_await delta::SemaphoreGetAwaiter{sem, count};
  ran.push_back(id);
}
