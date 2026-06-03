#pragma once

#include <coroutine>
#include <cstdint>
#include <deque>
#include <string>
#include <vector>

#include "common/types.h"

namespace delta {

enum class SemGetStatus : uint8_t { kAcquired, kBlock, kError };

struct SemaphoreObject {
  int32_t key_count = 0;
  std::vector<std::pair<int32_t, std::coroutine_handle<>>> waiters;

  explicit SemaphoreObject(int32_t initial_keys = 0)
      : key_count(initial_keys) {}

  bool Put(int32_t count = 1) {
    if (count < 0) return false;
    key_count += count;
    WakeWaiters();
    return true;
  }

  SemGetStatus Get(int32_t count = 1) {
    if (count < 0) return SemGetStatus::kError;
    if (key_count >= count) {
      key_count -= count;
      return SemGetStatus::kAcquired;
    }
    return SemGetStatus::kBlock;
  }

  int32_t TryGet(int32_t count = 1) {
    if (count < 0) return 0;
    if (key_count >= count) {
      key_count -= count;
      return 1;
    }
    return 0;
  }

  // §15.3.3: the waiting queue is FIFO and arrival order shall be preserved.
  // Drain strictly from the head: if the earliest-arrived waiter cannot yet be
  // satisfied, stop — a later, smaller request must not jump ahead of it. This
  // is the wakeup path invoked by put() (§15.3.2) to resume a process that was
  // suspended in get() (§15.3.3) once enough keys have been returned.
  void WakeWaiters() {
    while (!waiters.empty()) {
      auto& front = waiters.front();
      if (key_count < front.first) break;
      key_count -= front.first;
      auto h = front.second;
      waiters.erase(waiters.begin());
      h.resume();
    }
  }
};

enum class MbxPutStatus : uint8_t { kPlaced, kBlock };
enum class MbxGetStatus : uint8_t { kRetrieved, kBlock };
enum class MbxPeekStatus : uint8_t { kCopied, kBlock };

struct MailboxObject {
  int32_t bound = 0;
  std::deque<uint64_t> messages;
  std::vector<std::coroutine_handle<>> get_waiters;
  std::vector<std::coroutine_handle<>> peek_waiters;
  std::vector<std::coroutine_handle<>> put_waiters;

  explicit MailboxObject(int32_t b = 0) : bound(b < 0 ? 0 : b) {}

  int32_t Num() const { return static_cast<int32_t>(messages.size()); }

  MbxPutStatus Put(uint64_t msg) {
    if (IsFull()) return MbxPutStatus::kBlock;
    messages.push_back(msg);
    WakeGetWaiters();
    return MbxPutStatus::kPlaced;
  }

  int32_t TryPut(uint64_t msg) {
    if (IsFull()) return 0;
    messages.push_back(msg);
    WakeGetWaiters();
    return 1;
  }

  MbxGetStatus Get(uint64_t& msg) {
    if (messages.empty()) return MbxGetStatus::kBlock;
    msg = messages.front();
    messages.pop_front();
    WakePutWaiters();
    return MbxGetStatus::kRetrieved;
  }

  int32_t TryGet(uint64_t& msg) {
    if (messages.empty()) return 0;
    msg = messages.front();
    messages.pop_front();
    WakePutWaiters();
    return 1;
  }

  MbxPeekStatus Peek(uint64_t& msg) {
    if (messages.empty()) return MbxPeekStatus::kBlock;
    msg = messages.front();
    return MbxPeekStatus::kCopied;
  }

  int32_t TryPeek(uint64_t& msg) {
    if (messages.empty()) return 0;
    msg = messages.front();
    return 1;
  }

  bool IsFull() const { return bound > 0 && Num() >= bound; }

  void WakeGetWaiters() {
    if (messages.empty()) return;

    auto peeks = std::move(peek_waiters);
    peek_waiters.clear();
    for (auto h : peeks) h.resume();

    if (!get_waiters.empty() && !messages.empty()) {
      auto h = get_waiters.front();
      get_waiters.erase(get_waiters.begin());
      h.resume();
    }
  }

  void WakePutWaiters() {
    if (IsFull()) return;
    if (!put_waiters.empty()) {
      auto h = put_waiters.front();
      put_waiters.erase(put_waiters.begin());
      h.resume();
    }
  }
};

struct EventTriggeredState {
  uint64_t trigger_time_ticks = UINT64_MAX;
};

}
