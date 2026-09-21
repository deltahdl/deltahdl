#pragma once

#include <coroutine>
#include <cstdint>
#include <deque>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

// §8.4 (printed page 182 of ~/IEEE 1800-2023.pdf) compares two handles by the
// object each refers to, and §15.3 (printed 372) and §15.4 (printed 374) make a
// semaphore or mailbox variable a handle to its bucket or its queue, so the
// value the handle carries -- what `a == b`, `a != null` and `if (a)` read
// through the generic paths -- is the object's identity: its address folded
// to 64 bits. Every SemaphoreObject and MailboxObject of a run is
// arena-owned and neither freed nor moved, so the address is unique among
// them and stable, and it needs no counter that one of the construction
// sites -- a module's or a package's declaration, a class property's `new`,
// a test's own MailboxObject -- could miss; no object stands at 0, which
// stays the null handle. Null for no object. Every held object carried 1,
// so two mailboxes each built by its own `new` compared equal.
inline uint64_t SyncObjectIdentity(const void* obj) {
  return static_cast<uint64_t>(reinterpret_cast<uintptr_t>(obj));
}

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
  // ordinary keys-unavailable 0 — surfaced through the optional out-parameter
  // so a caller can tell the two zero results apart.
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
// §15.4.7 peek() shares get()'s run-time type check: a stored message whose
// type is not equivalent to the receiving variable's type yields a type error
// rather than a copy, so kTypeError joins the copied/blocked outcomes.
enum class MbxPeekStatus : uint8_t { kCopied, kBlock, kTypeError };

// §15.4.5: the data type a message was placed with, which a typeless mailbox
// keeps beside the message so that get(), try_get(), peek() and try_peek()
// can compare it against the type of the variable they are handed. The kinds
// are the ones §6.22.2 tells apart for a singular value: an integral type by
// its total bits, signedness and number of states (§6.22.2 c), a real by its
// own width, a string, and a class by its name (§6.22.1 a and d). kAny is the
// wildcard of a side whose type nobody recorded -- a computed actual, a
// selected target, or any message of a parameterized mailbox, whose types
// §15.4.9 has the compiler verify -- and it matches every type.
struct MailboxMessageType {
  enum class Kind : uint8_t { kAny, kIntegral, kReal, kString, kClass };
  // §6.22.2 c) separates a 2-state type from a 4-state one. A literal states
  // neither, so kUnknown stands where the count is not recorded and the
  // comparison passes over it.
  enum class States : uint8_t { kUnknown, kTwo, kFour };

  Kind kind = Kind::kAny;
  uint32_t width = 0;
  bool is_signed = false;
  States states = States::kUnknown;
  std::string_view class_name;

  static constexpr MailboxMessageType Integral(uint32_t width, bool is_signed,
                                               States states) {
    return {Kind::kIntegral, width, is_signed, states, {}};
  }
  static constexpr MailboxMessageType Real(uint32_t width) {
    return {Kind::kReal, width, false, States::kUnknown, {}};
  }
  static constexpr MailboxMessageType String() {
    return {Kind::kString, 0, false, States::kUnknown, {}};
  }
  static constexpr MailboxMessageType Class(std::string_view name) {
    return {Kind::kClass, 0, false, States::kUnknown, name};
  }

  // §6.22.2: whether two message types are equivalent. kAny on either side
  // never reports a mismatch. This single predicate is shared by the run-time
  // checks of get() (§15.4.5), try_get() (§15.4.6), peek() (§15.4.7) and
  // try_peek() (§15.4.8), and by the parameterized mailbox's element-type
  // contract (§15.4.9).
  bool EquivalentTo(const MailboxMessageType& other) const {
    if (kind == Kind::kAny || other.kind == Kind::kAny) return true;
    if (kind != other.kind) return false;
    switch (kind) {
      case Kind::kIntegral:
        return width == other.width && is_signed == other.is_signed &&
               (states == States::kUnknown ||
                other.states == States::kUnknown || states == other.states);
      case Kind::kReal:
        return width == other.width;
      case Kind::kClass:
        return class_name == other.class_name;
      default:
        return true;
    }
  }
};

struct MailboxObject {
  // §15.4.5: a nonparameterized (typeless) mailbox may carry messages of
  // differing types, so the implementation maintains the data type placed by
  // put() alongside each value to enable the run-time type check performed by
  // get()/try_get()/try_peek(). A default MailboxMessageType is the wildcard
  // used by callers that do not track a concrete type -- a fully dynamic
  // transfer that suppresses the mismatch report on whichever side carries it.
  //
  // §15.4.3: a message is any singular expression, so it is held whole as the
  // words of its value with the 4-state plane and the width, signedness, real
  // and string marks the evaluator gave it, in storage of the queue's own:
  // the value put() was handed may be a view of a variable's words, which
  // the variable's next assignment would rewrite under the queue.
  int32_t bound = 0;
  // §15.4.9: a parameterized mailbox fixes its element type up front; the
  // generic (dynamic) mailbox leaves this as the wildcard and is typeless.
  MailboxMessageType param_type;
  std::deque<Logic4Snapshot> messages;
  std::deque<MailboxMessageType> message_types;
  std::vector<std::coroutine_handle<>> get_waiters;
  std::vector<std::coroutine_handle<>> peek_waiters;
  std::vector<std::coroutine_handle<>> put_waiters;

  explicit MailboxObject(int32_t b = 0) : bound(b < 0 ? 0 : b) {}

  // §15.4.1: new() builds the mailbox with the bound it names, 0 leaving it
  // unbounded and a negative bound, which the subclause calls illegal, taken
  // as 0 as the constructor takes it. A variable given a later `mbx = new(N)`
  // names a fresh mailbox, so the messages of the one it named are gone; the
  // processes waiting on it keep their place, as an object no handle names
  // still resumes them.
  void Build(int32_t b) {
    bound = b < 0 ? 0 : b;
    messages.clear();
    message_types.clear();
  }

  // §15.4.9: the only difference between a generic mailbox and a parameterized
  // one is that the parameterized mailbox verifies argument types up front;
  // this predicate is the decision a parameterized mailbox applies to a value's
  // type.
  bool AcceptsType(const MailboxMessageType& type) const {
    return param_type.EquivalentTo(type);
  }

  int32_t Num() const { return static_cast<int32_t>(messages.size()); }

  MbxPutStatus Put(const Logic4Vec& msg, const MailboxMessageType& type = {}) {
    if (IsFull()) return MbxPutStatus::kBlock;
    Append(msg, type);
    return MbxPutStatus::kPlaced;
  }

  int32_t TryPut(const Logic4Vec& msg, const MailboxMessageType& type = {}) {
    if (IsFull()) return 0;
    Append(msg, type);
    return 1;
  }

  // §15.4.5: removes one message from the queue. If the queue is empty the
  // caller blocks; if the front message's type is not equivalent to the
  // retrieving variable's type a run-time type error is reported and the queue
  // is left untouched.
  MbxGetStatus Get(Logic4Snapshot& msg,
                   const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return MbxGetStatus::kBlock;
    if (!FrontMatches(expected_type)) return MbxGetStatus::kTypeError;
    Remove(msg);
    return MbxGetStatus::kRetrieved;
  }

  // §15.4.6: empty mailbox yields 0; a type that is not equivalent to the front
  // message yields a negative integer (the message is left in place); otherwise
  // the message is removed and a positive integer is returned.
  int32_t TryGet(Logic4Snapshot& msg,
                 const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return 0;
    if (!FrontMatches(expected_type)) return -1;
    Remove(msg);
    return 1;
  }

  // §15.4.7: copies the front message but, unlike get(), leaves it in the
  // queue. An empty mailbox blocks the caller until a message is placed. As in
  // get(), a stored message whose type is not equivalent to the receiving
  // variable's type generates a run-time type error and the message is left
  // untouched rather than copied out.
  MbxPeekStatus Peek(Logic4Snapshot& msg,
                     const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return MbxPeekStatus::kBlock;
    if (!FrontMatches(expected_type)) return MbxPeekStatus::kTypeError;
    msg = messages.front();
    return MbxPeekStatus::kCopied;
  }

  // §15.4.8: like try_get() but the message is never removed; empty yields 0, a
  // non-equivalent type yields a negative integer, a match yields a positive
  // integer with the message copied out.
  int32_t TryPeek(Logic4Snapshot& msg,
                  const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return 0;
    if (!FrontMatches(expected_type)) return -1;
    msg = messages.front();
    return 1;
  }

  bool IsFull() const { return bound > 0 && Num() >= bound; }

  bool FrontMatches(const MailboxMessageType& expected_type) const {
    return message_types.front().EquivalentTo(expected_type);
  }

  // §15.4.3 and §15.4.4: the message joins the tail of the queue, in strict
  // FIFO order, copied into the queue's own words, and a process waiting for
  // one is woken.
  void Append(const Logic4Vec& msg, const MailboxMessageType& type) {
    messages.emplace_back().Capture(msg);
    message_types.push_back(type);
    WakeGetWaiters();
  }

  // §15.4.5 and §15.4.6: the front message leaves the queue into `msg`, and a
  // process waiting for room is woken.
  void Remove(Logic4Snapshot& msg) {
    msg = std::move(messages.front());
    PopFront();
    WakePutWaiters();
  }

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

}  // namespace delta
