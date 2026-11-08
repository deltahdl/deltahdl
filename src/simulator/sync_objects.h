#pragma once

#include <cstdint>
#include <deque>
#include <functional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

inline uint64_t SyncObjectIdentity(const void* obj) {
  return static_cast<uint64_t>(reinterpret_cast<uintptr_t>(obj));
}

enum class SemGetStatus : uint8_t { kAcquired, kBlock, kError };

struct SemaphoreObject {
  int32_t key_count = 0;
  bool shared = false;
  std::vector<std::pair<int32_t, std::function<void()>>> waiters;

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

  void WakeWaiters() {
    while (!waiters.empty()) {
      auto& front = waiters.front();
      if (key_count < front.first) break;
      key_count -= front.first;
      auto resume = std::move(front.second);
      waiters.erase(waiters.begin());
      resume();
    }
  }
};

enum class MbxPutStatus : uint8_t { kPlaced, kBlock };
enum class MbxGetStatus : uint8_t { kRetrieved, kBlock, kTypeError };
enum class MbxPeekStatus : uint8_t { kCopied, kBlock, kTypeError };

struct MailboxMessageType {
  enum class Kind : uint8_t { kAny, kIntegral, kReal, kString, kClass };
  enum class States : uint8_t { kUnknown, kTwo, kFour };

  Kind kind = Kind::kAny;
  uint32_t width = 0;
  bool is_signed = false;
  States states = States::kUnknown;
  std::string_view class_name;
  Kind value_kind = Kind::kAny;

  static constexpr MailboxMessageType Integral(uint32_t width, bool is_signed,
                                               States states) {
    return {Kind::kIntegral, width, is_signed, states, {}, Kind::kIntegral};
  }
  static constexpr MailboxMessageType Real(uint32_t width) {
    return {Kind::kReal, width, false, States::kUnknown, {}, Kind::kReal};
  }
  static constexpr MailboxMessageType String() {
    return {Kind::kString, 0, false, States::kUnknown, {}, Kind::kString};
  }
  static constexpr MailboxMessageType Class(std::string_view name) {
    return {Kind::kClass, 0, false, States::kUnknown, name, Kind::kClass};
  }

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
  bool shared = false;
  int32_t bound = 0;
  MailboxMessageType param_type;
  std::deque<Logic4Snapshot> messages;
  std::deque<MailboxMessageType> message_types;
  std::vector<std::function<void()>> get_waiters;
  std::vector<std::function<void()>> peek_waiters;
  std::vector<std::function<void()>> put_waiters;

  explicit MailboxObject(int32_t b = 0) : bound(b < 0 ? 0 : b) {}

  void Build(int32_t b) {
    bound = b < 0 ? 0 : b;
    messages.clear();
    message_types.clear();
  }

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

  MbxGetStatus Get(Logic4Snapshot& msg,
                   const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return MbxGetStatus::kBlock;
    if (!FrontMatches(expected_type)) return MbxGetStatus::kTypeError;
    Remove(msg);
    return MbxGetStatus::kRetrieved;
  }

  int32_t TryGet(Logic4Snapshot& msg,
                 const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return 0;
    if (!FrontMatches(expected_type)) return -1;
    Remove(msg);
    return 1;
  }

  MbxPeekStatus Peek(Logic4Snapshot& msg,
                     const MailboxMessageType& expected_type = {}) {
    if (messages.empty()) return MbxPeekStatus::kBlock;
    if (!FrontMatches(expected_type)) return MbxPeekStatus::kTypeError;
    msg = messages.front();
    return MbxPeekStatus::kCopied;
  }

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

  void Append(const Logic4Vec& msg, const MailboxMessageType& type) {
    messages.emplace_back().Capture(msg);
    message_types.push_back(type);
    WakeGetWaiters();
  }

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
    for (auto& resume : peeks) resume();

    if (!get_waiters.empty() && !messages.empty()) {
      auto resume = std::move(get_waiters.front());
      get_waiters.erase(get_waiters.begin());
      resume();
    }
  }

  void WakePutWaiters() {
    if (IsFull()) return;
    if (!put_waiters.empty()) {
      auto resume = std::move(put_waiters.front());
      put_waiters.erase(put_waiters.begin());
      resume();
    }
  }
};

struct EventTriggeredState {
  uint64_t trigger_time_ticks = UINT64_MAX;
};

}  // namespace delta
