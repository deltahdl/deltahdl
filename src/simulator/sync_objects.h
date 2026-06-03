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

  // §15.3.4: non-blocking procure. When enough keys are available the bucket is
  // drained by count and a positive value is returned; otherwise 0 is returned
  // and the bucket is left untouched (no blocking, unlike get()). A negative
  // count yields 0 as well, but is additionally an error — distinct from the
  // ordinary keys-unavailable 0 — surfaced through the optional out-parameter so
  // a caller can tell the two zero results apart.
  int32_t TryGet(int32_t count = 1, bool* error = nullptr) {
    if (count < 0) {
      if (error) *error = true;
      return 0;
    }
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

// §15.4.5 adds kTypeError: when the type of the message variable handed to
// get() is not equivalent to the type of the message held at the front of the
// queue, a run-time error is generated rather than a value retrieved.
enum class MbxPutStatus : uint8_t { kPlaced, kBlock };
enum class MbxGetStatus : uint8_t { kRetrieved, kBlock, kTypeError };
enum class MbxPeekStatus : uint8_t { kCopied, kBlock };

struct MailboxObject {
  // §15.4.5: a nonparameterized (typeless) mailbox may carry messages of
  // differing types, so the implementation maintains the data type placed by
  // put() alongside each value to enable the run-time type check performed by
  // get()/try_get()/try_peek(). kAnyType is the wildcard used by callers that
  // do not track a concrete type — a fully dynamic transfer that suppresses the
  // mismatch report on whichever side carries it.
  static constexpr uint32_t kAnyType = 0;

  int32_t bound = 0;
  // §15.4.9: a parameterized mailbox fixes its element type up front; the
  // generic (dynamic) mailbox leaves this as kAnyType and is typeless.
  uint32_t param_type = kAnyType;
  std::deque<uint64_t> messages;
  std::deque<uint32_t> message_types;
  std::vector<std::coroutine_handle<>> get_waiters;
  std::vector<std::coroutine_handle<>> peek_waiters;
  std::vector<std::coroutine_handle<>> put_waiters;

  explicit MailboxObject(int32_t b = 0) : bound(b < 0 ? 0 : b) {}

  // Two message types match when they share an id. kAnyType acts as a wildcard:
  // a dynamic transfer (untracked on either side) never reports a mismatch.
  // This single predicate is shared by the run-time checks of get() (§15.4.5),
  // try_get() (§15.4.6) and try_peek() (§15.4.8), and by the parameterized
  // mailbox's element-type contract (§15.4.9).
  static bool TypesEquivalent(uint32_t a, uint32_t b) {
    return a == kAnyType || b == kAnyType || a == b;
  }

  // §15.4.9: the only difference between a generic mailbox and a parameterized
  // one is that the parameterized mailbox verifies argument types up front; this
  // predicate is the decision a parameterized mailbox applies to a value's type.
  bool AcceptsType(uint32_t type) const {
    return TypesEquivalent(param_type, type);
  }

  int32_t Num() const { return static_cast<int32_t>(messages.size()); }

  MbxPutStatus Put(uint64_t msg, uint32_t type = kAnyType) {
    if (IsFull()) return MbxPutStatus::kBlock;
    messages.push_back(msg);
    message_types.push_back(type);
    WakeGetWaiters();
    return MbxPutStatus::kPlaced;
  }

  int32_t TryPut(uint64_t msg, uint32_t type = kAnyType) {
    if (IsFull()) return 0;
    messages.push_back(msg);
    message_types.push_back(type);
    WakeGetWaiters();
    return 1;
  }

  // §15.4.5: removes one message from the queue. If the queue is empty the
  // caller blocks; if the front message's type is not equivalent to the
  // retrieving variable's type a run-time type error is reported and the queue
  // is left untouched.
  MbxGetStatus Get(uint64_t& msg, uint32_t expected_type = kAnyType) {
    if (messages.empty()) return MbxGetStatus::kBlock;
    if (!TypesEquivalent(message_types.front(), expected_type))
      return MbxGetStatus::kTypeError;
    msg = messages.front();
    PopFront();
    WakePutWaiters();
    return MbxGetStatus::kRetrieved;
  }

  // §15.4.6: empty mailbox yields 0; a type that is not equivalent to the front
  // message yields a negative integer (the message is left in place); otherwise
  // the message is removed and a positive integer is returned.
  int32_t TryGet(uint64_t& msg, uint32_t expected_type = kAnyType) {
    if (messages.empty()) return 0;
    if (!TypesEquivalent(message_types.front(), expected_type)) return -1;
    msg = messages.front();
    PopFront();
    WakePutWaiters();
    return 1;
  }

  MbxPeekStatus Peek(uint64_t& msg) {
    if (messages.empty()) return MbxPeekStatus::kBlock;
    msg = messages.front();
    return MbxPeekStatus::kCopied;
  }

  // §15.4.8: like try_get() but the message is never removed; empty yields 0, a
  // non-equivalent type yields a negative integer, a match yields a positive
  // integer with the message copied out.
  int32_t TryPeek(uint64_t& msg, uint32_t expected_type = kAnyType) {
    if (messages.empty()) return 0;
    if (!TypesEquivalent(message_types.front(), expected_type)) return -1;
    msg = messages.front();
    return 1;
  }

  bool IsFull() const { return bound > 0 && Num() >= bound; }

  void PopFront() {
    messages.pop_front();
    message_types.pop_front();
  }

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
