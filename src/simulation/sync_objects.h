#pragma once

#include <coroutine>
#include <cstdint>
#include <deque>
#include <string>
#include <vector>

#include "common/types.h"

namespace delta {

// --- Semaphore (IEEE 1800-2023 section 15.3) ---
// A counting semaphore for interprocess synchronization.
// Processes block on get() when insufficient keys are available.

struct SemaphoreObject {
  int32_t key_count = 0;
  std::vector<std::pair<int32_t, std::coroutine_handle<>>> waiters;

  explicit SemaphoreObject(int32_t initial_keys = 0)
      : key_count(initial_keys) {}

  // section 15.3.2: Add keys. Returns void; wakes waiters if possible.
  void Put(int32_t count = 1) {
    key_count += count;
    WakeWaiters();
  }

  // section 15.3.3: Non-blocking get. Returns 1 on success, 0 on failure.
  int32_t TryGet(int32_t count = 1) {
    if (key_count >= count) {
      key_count -= count;
      return 1;
    }
    return 0;
  }

  // Wake waiters whose key requests can now be satisfied.
  void WakeWaiters() {
    auto it = waiters.begin();
    while (it != waiters.end()) {
      if (key_count >= it->first) {
        key_count -= it->first;
        auto h = it->second;
        it = waiters.erase(it);
        h.resume();
      } else {
        ++it;
      }
    }
  }
};

// --- Mailbox (IEEE 1800-2023 section 15.4) ---
// A bounded or unbounded FIFO queue for message passing between processes.

struct MailboxObject {
  int32_t bound = 0;  // 0 means unbounded.
  std::deque<uint64_t> messages;
  std::vector<std::coroutine_handle<>> get_waiters;
  std::vector<std::coroutine_handle<>> peek_waiters;
  std::vector<std::coroutine_handle<>> put_waiters;

  explicit MailboxObject(int32_t b = 0) : bound(b) {}

  // section 15.4.2: Number of messages.
  int32_t Num() const { return static_cast<int32_t>(messages.size()); }

  // section 15.4.3: Non-blocking put. Returns 0 on success, -1 if full.
  int32_t TryPut(uint64_t msg) {
    if (bound > 0 && Num() >= bound) return -1;
    messages.push_back(msg);
    WakeGetWaiters();
    return 0;
  }

  // section 15.4.4: Non-blocking get. Returns 0 on success, -1 if empty.
  int32_t TryGet(uint64_t& msg) {
    if (messages.empty()) return -1;
    msg = messages.front();
    messages.pop_front();
    WakePutWaiters();
    return 0;
  }

  // section 15.4.5: Non-blocking peek. Returns 0 on success, -1 if empty.
  int32_t TryPeek(uint64_t& msg) {
    if (messages.empty()) return -1;
    msg = messages.front();
    return 0;
  }

  bool IsFull() const { return bound > 0 && Num() >= bound; }

  void WakeGetWaiters() {
    if (messages.empty()) return;
    // Wake peek waiters first (they don't consume).
    auto peeks = std::move(peek_waiters);
    peek_waiters.clear();
    for (auto h : peeks) h.resume();
    // Wake one get waiter.
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

// --- Event triggered state (IEEE 1800-2023 section 15.5.2) ---
// Tracks the sticky .triggered property within a timeslot.

struct EventTriggeredState {
  uint64_t trigger_time_ticks = UINT64_MAX;  // Timeslot when last triggered.
};

}  // namespace delta
