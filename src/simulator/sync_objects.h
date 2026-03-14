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

enum class SemGetStatus : uint8_t { kAcquired, kBlock, kError };

struct SemaphoreObject {
  int32_t key_count = 0;
  std::vector<std::pair<int32_t, std::coroutine_handle<>>> waiters;

  explicit SemaphoreObject(int32_t initial_keys = 0)
      : key_count(initial_keys) {}

  // §15.3.2: Return keys. Returns false if count is negative (error).
  bool Put(int32_t count = 1) {
    if (count < 0) return false;
    key_count += count;
    WakeWaiters();
    return true;
  }

  // §15.3.3: Blocking get. Reduces key_count if enough keys are available.
  // Returns kAcquired on success, kBlock if caller must suspend, kError
  // if count is negative.
  SemGetStatus Get(int32_t count = 1) {
    if (count < 0) return SemGetStatus::kError;
    if (key_count >= count) {
      key_count -= count;
      return SemGetStatus::kAcquired;
    }
    return SemGetStatus::kBlock;
  }

  // §15.3.4: Non-blocking get. Returns 1 on success, 0 on failure.
  // Negative keyCount returns 0 (error).
  int32_t TryGet(int32_t count = 1) {
    if (count < 0) return 0;
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

enum class MbxPutStatus : uint8_t { kPlaced, kBlock };
enum class MbxGetStatus : uint8_t { kRetrieved, kBlock };
enum class MbxPeekStatus : uint8_t { kCopied, kBlock };

struct MailboxObject {
  int32_t bound = 0;  // 0 means unbounded.
  std::deque<uint64_t> messages;
  std::vector<std::coroutine_handle<>> get_waiters;
  std::vector<std::coroutine_handle<>> peek_waiters;
  std::vector<std::coroutine_handle<>> put_waiters;

  // §15.4.1: Negative bounds are illegal; clamp to 0 (unbounded).
  explicit MailboxObject(int32_t b = 0) : bound(b < 0 ? 0 : b) {}

  // section 15.4.2: Number of messages.
  int32_t Num() const { return static_cast<int32_t>(messages.size()); }

  // §15.4.3: Blocking put. Places message in FIFO order.
  // Returns kPlaced on success, kBlock if the caller must suspend (bounded & full).
  // Unbounded mailboxes always return kPlaced.
  MbxPutStatus Put(uint64_t msg) {
    if (IsFull()) return MbxPutStatus::kBlock;
    messages.push_back(msg);
    WakeGetWaiters();
    return MbxPutStatus::kPlaced;
  }

  // §15.4.4: Non-blocking put. Returns positive int on success, 0 if full.
  int32_t TryPut(uint64_t msg) {
    if (IsFull()) return 0;
    messages.push_back(msg);
    WakeGetWaiters();
    return 1;
  }

  // §15.4.5: Blocking get. Retrieves and removes front message.
  // Returns kRetrieved on success, kBlock if the caller must suspend (empty).
  MbxGetStatus Get(uint64_t& msg) {
    if (messages.empty()) return MbxGetStatus::kBlock;
    msg = messages.front();
    messages.pop_front();
    WakePutWaiters();
    return MbxGetStatus::kRetrieved;
  }

  // §15.4.6: Non-blocking get. Returns positive int on success, 0 if empty.
  int32_t TryGet(uint64_t& msg) {
    if (messages.empty()) return 0;
    msg = messages.front();
    messages.pop_front();
    WakePutWaiters();
    return 1;
  }

  // §15.4.7: Blocking peek. Copies front message without removing it.
  // Returns kCopied on success, kBlock if the caller must suspend (empty).
  MbxPeekStatus Peek(uint64_t& msg) {
    if (messages.empty()) return MbxPeekStatus::kBlock;
    msg = messages.front();
    return MbxPeekStatus::kCopied;
  }

  // §15.4.8: Non-blocking peek. Returns positive int on success, 0 if empty.
  int32_t TryPeek(uint64_t& msg) {
    if (messages.empty()) return 0;
    msg = messages.front();
    return 1;
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
