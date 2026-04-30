#pragma once

#include <array>
#include <cstdint>
#include <functional>
#include <map>

#include "common/types.h"

namespace delta {

// --- Event types for the stratified scheduler ---

enum class EventKind : uint8_t {
  kUpdate,
  kEvaluation,
};

struct Event {
  EventKind kind = EventKind::kEvaluation;
  void* target = nullptr;
  std::function<void()> callback;
  Event* next = nullptr;
};

// --- Intrusive linked-list event queue ---

struct EventQueue {
  Event* head = nullptr;
  Event* tail = nullptr;

  void Push(Event* event);
  Event* Pop();
  bool empty() const { return head == nullptr; }
  void Clear();
};

// --- Time slot: one queue per region ---

struct TimeSlot {
  std::array<EventQueue, kRegionCount> regions{};

  bool AnyNonemptyIn(Region first, Region last) const;

  // §4.4.1 ¶2: true while any iterative region in this slot still holds
  // events, decided by routing each region through IsIterativeRegion so the
  // outer iterative loop applies the §4.4.1 ¶2 classification rather than a
  // hard-coded enum range.
  bool AnyIterativeNonempty() const;
};

// --- Forward declaration ---

class Arena;

// --- Event pool (free-list recycler) ---

class EventPool {
 public:
  explicit EventPool(Arena& arena) : arena_(arena) {}

  /// Acquire an event: pop from free-list or allocate from arena.
  Event* Acquire();

  /// Release an event back to the free-list for reuse.
  void Release(Event* event);

  /// Number of events currently in the free-list.
  size_t FreeCount() const { return free_count_; }

 private:
  Arena& arena_;
  Event* free_list_ = nullptr;
  size_t free_count_ = 0;
};

// --- Stratified event scheduler (IEEE 1800-2023 section 4.5) ---

class Scheduler {
 public:
  explicit Scheduler(Arena& arena) : pool_(arena) {}

  SimTime CurrentTime() const { return current_time_; }
  Region CurrentRegion() const { return current_region_; }
  bool HasEvents() const { return !event_calendar_.empty(); }

  void ScheduleEvent(SimTime time, Region region, Event* event);
  void Run();

  EventPool& GetEventPool() { return pool_; }

  void SetPostTimestepCallback(std::function<void()> cb) {
    post_timestep_cb_ = std::move(cb);
  }

  // §4.4.3.1: Number of attempts to schedule an event in any other region of
  // the current time slot from inside the Preponed region. Such schedules are
  // declared illegal by the LRM; the scheduler still queues the event but
  // records the violation here so callers can detect the rule break.
  size_t IllegalPreponedScheduleCount() const {
    return illegal_preponed_schedule_count_;
  }

  // §4.4.3.1: Number of attempts to write a net or variable while inside the
  // Preponed region. Production write paths (e.g. VpiContext::PutValue) call
  // NoteWriteAttempt() before mutating a net or variable; the scheduler
  // increments this counter when the current region is Preponed, applying
  // the LRM's "illegal to write values to any net or variable" restriction.
  size_t IllegalPreponedWriteCount() const {
    return illegal_preponed_write_count_;
  }

  // §4.4.2.9: Within the Postponed region it is illegal to schedule an event
  // in any previous region within the current time slot. Postponed is the
  // last region of the slot, so any current-time schedule into a non-Postponed
  // region is a violation. The scheduler still queues the event so that
  // non-conforming code stays observable.
  size_t IllegalPostponedScheduleCount() const {
    return illegal_postponed_schedule_count_;
  }

  // §4.4.2.9: Within the Postponed region it is illegal to write values to
  // any net or variable. Production write paths (e.g. VpiContext::PutValue)
  // call NoteWriteAttempt() before mutating a net or variable; the scheduler
  // increments this counter when the current region is Postponed, applying
  // the §4.4.2.9 "no new value changes" restriction. §4.4.3.10 PLI events
  // share this same Postponed region, so PLI callback writes are caught here.
  size_t IllegalPostponedWriteCount() const {
    return illegal_postponed_write_count_;
  }

  // §4.3 ¶3: every change in state of a net or variable is an *update event*.
  // Counts events that production code labels EventKind::kUpdate at the
  // moment they enter the calendar, so a test can observe that a state-change
  // path applied the §4.3 ¶3 classification rather than reading state values.
  size_t UpdateEventScheduledCount() const {
    return update_events_scheduled_count_;
  }

  // §4.3 ¶4: the evaluation of a process is an *evaluation event*. Counts
  // events that production code labels EventKind::kEvaluation when scheduled,
  // letting a test observe that process-evaluation paths applied the §4.3 ¶4
  // classification.
  size_t EvaluationEventScheduledCount() const {
    return evaluation_events_scheduled_count_;
  }

  // §4.4.3.1 and §4.4.2.9: Called by net/variable write paths before each
  // write. The Preponed region forbids writes (§4.4.3.1) and the Postponed
  // region forbids writes (§4.4.2.9, "no new value changes"). The scheduler
  // records each violation in its own counter so callers can attribute the
  // rule break to the right subclause.
  void NoteWriteAttempt() {
    if (current_region_ == Region::kPreponed) {
      ++illegal_preponed_write_count_;
    } else if (current_region_ == Region::kPostponed) {
      ++illegal_postponed_write_count_;
    }
  }

 private:
  void ExecuteTimeSlot(TimeSlot& slot);
  void ExecuteActiveRegions(TimeSlot& slot);
  void ExecuteReactiveRegions(TimeSlot& slot);
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
  size_t update_events_scheduled_count_ = 0;
  size_t evaluation_events_scheduled_count_ = 0;
  bool stop_requested_ = false;
};

}  // namespace delta
