#pragma once

#include <array>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>

#include "common/types.h"

namespace delta {

enum class EventKind : uint8_t {
  kUpdate,
  kEvaluation,
  kPli,
};

struct Event {
  EventKind kind = EventKind::kEvaluation;
  void* target = nullptr;
  std::function<void()> callback;
  Event* next = nullptr;
  // When set and pointing at a true value, this event has been superseded and
  // does no work (an inertial-delay timeout an operand change cancelled, IEEE
  // 1800 §28). Such an event must not advance simulation time. Null for every
  // ordinary event, which is always live.
  std::shared_ptr<bool> superseded = nullptr;
};

struct EventQueue {
  Event* head = nullptr;
  Event* tail = nullptr;

  void Push(Event* event);
  Event* Pop();
  bool empty() const { return head == nullptr; }
  void Clear();
};

struct TimeSlot {
  std::array<EventQueue, kRegionCount> regions{};

  bool AnyNonemptyIn(Region first, Region last) const;

  // Lowest-ordinal region in [first, last] holding an event, or kCOUNT when the
  // whole range is empty. Drives the §4.5 earliest-nonempty-first iteration.
  Region FirstNonemptyIn(Region first, Region last) const;

  bool AnyIterativeNonempty() const;
};

class Arena;

class EventPool {
 public:
  explicit EventPool(Arena& arena) : arena_(arena) {}

  Event* Acquire();

  void Release(Event* event);

  size_t FreeCount() const { return free_count_; }

 private:
  Arena& arena_;
  Event* free_list_ = nullptr;
  size_t free_count_ = 0;
};

class Scheduler {
 public:
  explicit Scheduler(Arena& arena) : pool_(arena) {}

  SimTime CurrentTime() const { return current_time_; }

  // The time of the earliest event still scheduled - the next future event.
  // When nothing remains queued there is no future event, so the current time
  // is reported instead. Events at or before current_time_ are skipped: while
  // the current time slot is being drained its entry is still present, and a
  // query for the next event (e.g. §38.13 time-queue) must report only future
  // work.
  SimTime NextEventTime() const {
    if (event_calendar_.empty()) return current_time_;
    auto it = event_calendar_.upper_bound(current_time_);
    if (it == event_calendar_.end()) return current_time_;
    return it->first;
  }

  Region CurrentRegion() const { return current_region_; }
  bool HasEvents() const { return !event_calendar_.empty(); }

  void ScheduleEvent(SimTime time, Region region, Event* event);
  void Run();

  EventPool& GetEventPool() { return pool_; }

  void SetPostTimestepCallback(std::function<void()> cb) {
    post_timestep_cb_ = std::move(cb);
  }

  size_t IllegalPreponedScheduleCount() const {
    return illegal_preponed_schedule_count_;
  }

  size_t IllegalPreponedWriteCount() const {
    return illegal_preponed_write_count_;
  }

  size_t IllegalPostponedScheduleCount() const {
    return illegal_postponed_schedule_count_;
  }

  size_t IllegalPostponedWriteCount() const {
    return illegal_postponed_write_count_;
  }

  size_t IllegalObservedPliCount() const { return illegal_observed_pli_count_; }

  // §4.4.3.5: the Pre-Observed region is read-only - it is illegal to schedule
  // an event into the current time slot or to write a net or variable from
  // within it. Each violation attempt is tallied here.
  size_t IllegalPreObservedScheduleCount() const {
    return illegal_pre_observed_schedule_count_;
  }

  size_t IllegalPreObservedWriteCount() const {
    return illegal_pre_observed_write_count_;
  }

  size_t UpdateEventScheduledCount() const {
    return update_events_scheduled_count_;
  }

  size_t EvaluationEventScheduledCount() const {
    return evaluation_events_scheduled_count_;
  }

  void NoteWriteAttempt() {
    if (current_region_ == Region::kPreponed) {
      ++illegal_preponed_write_count_;
    } else if (current_region_ == Region::kPostponed) {
      ++illegal_postponed_write_count_;
    } else if (current_region_ == Region::kPreObserved) {
      ++illegal_pre_observed_write_count_;
    }
  }

  static bool IsAnyOrderRegion(Region r) {
    return r == Region::kActive || r == Region::kReactive;
  }

  static constexpr bool AllowsUserOrderControl() { return false; }

  void NoteMidStatementSuspension() { ++mid_statement_suspension_count_; }
  size_t MidStatementSuspensionCount() const {
    return mid_statement_suspension_count_;
  }

  static constexpr Region HomeRegionForReactiveBlockingAssign() {
    return Region::kReactive;
  }

  static constexpr Region ReactiveSetDualOf(Region active) {
    switch (active) {
      case Region::kActive:
        return Region::kReactive;
      case Region::kInactive:
        return Region::kReInactive;
      case Region::kNBA:
        return Region::kReNBA;
      default:
        return Region::kCOUNT;
    }
  }

 private:
  void ExecuteTimeSlot(TimeSlot& slot);
  void ExecuteRegion(TimeSlot& slot, Region region);
  void DrainQueue(EventQueue& queue);

  bool IterateActiveSet(TimeSlot& slot);
  bool IterateReactiveSet(TimeSlot& slot);

  EventPool pool_;
  std::map<SimTime, TimeSlot> event_calendar_;
  std::function<void()> post_timestep_cb_;
  SimTime current_time_{0};
  Region current_region_ = Region::kCOUNT;
  size_t illegal_preponed_schedule_count_ = 0;
  size_t illegal_preponed_write_count_ = 0;
  size_t illegal_postponed_schedule_count_ = 0;
  size_t illegal_postponed_write_count_ = 0;
  size_t illegal_observed_pli_count_ = 0;
  size_t illegal_pre_observed_schedule_count_ = 0;
  size_t illegal_pre_observed_write_count_ = 0;
  size_t update_events_scheduled_count_ = 0;
  size_t evaluation_events_scheduled_count_ = 0;
  size_t mid_statement_suspension_count_ = 0;
  bool stop_requested_ = false;
};

}  // namespace delta
