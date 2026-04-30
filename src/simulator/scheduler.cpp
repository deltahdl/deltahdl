#include "simulator/scheduler.h"

#include <cstdio>
#include <cstdlib>

#include "common/arena.h"

namespace delta {

// --- EventPool ---

Event* EventPool::Acquire() {
  if (free_list_) {
    Event* event = free_list_;
    free_list_ = event->next;
    --free_count_;
    event->next = nullptr;
    return event;
  }
  return arena_.Create<Event>();
}

void EventPool::Release(Event* event) {
  event->kind = EventKind::kEvaluation;
  event->target = nullptr;
  event->callback = nullptr;
  event->next = free_list_;
  free_list_ = event;
  ++free_count_;
}

// --- EventQueue ---

void EventQueue::Push(Event* event) {
  event->next = nullptr;
  if (tail) {
    tail->next = event;
  } else {
    head = event;
  }
  tail = event;
}

Event* EventQueue::Pop() {
  if (!head) {
    return nullptr;
  }
  Event* event = head;
  head = head->next;
  if (!head) {
    tail = nullptr;
  }
  event->next = nullptr;
  return event;
}

void EventQueue::Clear() {
  head = nullptr;
  tail = nullptr;
}

// --- TimeSlot ---

bool TimeSlot::AnyNonemptyIn(Region first, Region last) const {
  auto lo = static_cast<size_t>(first);
  auto hi = static_cast<size_t>(last);
  for (size_t i = lo; i <= hi; ++i) {
    if (!regions[i].empty()) {
      return true;
    }
  }
  return false;
}

bool TimeSlot::AnyIterativeNonempty() const {
  for (size_t i = 0; i < kRegionCount; ++i) {
    if (IsIterativeRegion(static_cast<Region>(i)) && !regions[i].empty()) {
      return true;
    }
  }
  return false;
}

// --- Scheduler: public interface ---

void Scheduler::ScheduleEvent(SimTime time, Region region, Event* event) {
  // §4.4 ¶2: every event has one simulation time which "can be the current
  // time or some future time", and "the simulator never goes backwards in
  // time". Enforce in every build configuration so a release simulator
  // cannot silently violate the rule on caller misuse.
  if (time < current_time_) {
    std::fprintf(
        stderr,
        "scheduler: refusing to schedule event at past time %llu "
        "(current=%llu); §4.4 ¶2 forbids backwards-in-time scheduling\n",
        static_cast<unsigned long long>(time.ticks),
        static_cast<unsigned long long>(current_time_.ticks));
    std::abort();
  }
  // §4.4.3.1: Within the Preponed region, it is illegal to schedule an
  // event in any other region within the current time slot.
  if (current_region_ == Region::kPreponed && time == current_time_ &&
      region != Region::kPreponed) {
    ++illegal_preponed_schedule_count_;
  }
  // §4.4.2.9: Within the Postponed region, it is illegal to schedule an
  // event in any previous region within the current time slot. Postponed
  // is the last region of the slot, so any current-time schedule into a
  // non-Postponed region is a violation. §4.4.3.10 PLI events share this
  // same Postponed region, so PLI callback schedules are caught here too.
  if (current_region_ == Region::kPostponed && time == current_time_ &&
      region != Region::kPostponed) {
    ++illegal_postponed_schedule_count_;
  }
  // §4.3 ¶3/¶4: tally each event by its kind at schedule time so a test can
  // observe that production code labelled the event as an update or
  // evaluation event in the calendar entry, before Run() releases the Event
  // back to the pool and clears its kind.
  if (event->kind == EventKind::kUpdate) {
    ++update_events_scheduled_count_;
  } else {
    ++evaluation_events_scheduled_count_;
  }
  auto idx = static_cast<size_t>(region);
  event_calendar_[time].regions[idx].Push(event);
}

void Scheduler::Run() {
  while (!event_calendar_.empty() && !stop_requested_) {
    auto it = event_calendar_.begin();
    current_time_ = it->first;
    ExecuteTimeSlot(it->second);
    event_calendar_.erase(it);
  }
}

// --- Scheduler: time slot execution (IEEE 1800-2023 section 4.5) ---

void Scheduler::ExecuteTimeSlot(TimeSlot& slot) {
  // Preponed region: read-only sampling (§4.4.2.1)
  ExecuteRegion(slot, Region::kPreponed);

  // Pre-Active region: PLI callback (§4.4.3.2)
  ExecuteRegion(slot, Region::kPreActive);

  // §4.4.1 ¶2: loop while any iterative region in this slot still holds
  // events. AnyIterativeNonempty routes each region through IsIterativeRegion
  // so the loop's gate is the §4.4.1 ¶2 classifier rather than a hard-coded
  // enum range.
  while (slot.AnyIterativeNonempty()) {
    while (IterateActiveSet(slot)) {
    }
    while (IterateReactiveSet(slot)) {
    }
    // Pre-Postponed only when [Active...Post-Re-NBA] are all empty
    if (!slot.AnyNonemptyIn(Region::kActive, Region::kPostReNBA)) {
      ExecuteRegion(slot, Region::kPrePostponed);
    }
  }

  // Postponed region: read-only (§4.4.3.10)
  ExecuteRegion(slot, Region::kPostponed);

  current_region_ = Region::kCOUNT;
  if (post_timestep_cb_) post_timestep_cb_();
}

// Inner active-set loop: iterates over Active..Post-Observed per §4.5.

bool Scheduler::IterateActiveSet(TimeSlot& slot) {
  if (!slot.AnyNonemptyIn(Region::kActive, Region::kPostObserved)) {
    return false;
  }
  while (slot.AnyNonemptyIn(Region::kActive, Region::kPostObserved)) {
    ExecuteActiveRegions(slot);
  }
  return true;
}

void Scheduler::ExecuteActiveRegions(TimeSlot& slot) {
  // §4.4.1 ¶1: drain every active region set member in enum order, then bridge
  // through the Observed regions on the way to the reactive set (§4.5).
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsActiveRegionSet(r) || r == Region::kPreObserved ||
        r == Region::kObserved || r == Region::kPostObserved) {
      ExecuteRegion(slot, r);
    }
  }
}

// Inner reactive-set loop: iterates over Reactive..Post-Re-NBA per §4.5.
// The outer loop in ExecuteTimeSlot re-enters the active-set loop once this
// returns, so events scheduled into the active set during reactive drain are
// processed only after the five reactive regions are fully drained.

bool Scheduler::IterateReactiveSet(TimeSlot& slot) {
  if (!slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    return false;
  }
  while (slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    ExecuteReactiveRegions(slot);
  }
  return true;
}

void Scheduler::ExecuteReactiveRegions(TimeSlot& slot) {
  // §4.4.1 ¶1: drain every reactive region set member in enum order.
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsReactiveRegionSet(r)) {
      ExecuteRegion(slot, r);
    }
  }
}

// --- Scheduler: single region drain ---

void Scheduler::ExecuteRegion(TimeSlot& slot, Region region) {
  current_region_ = region;
  DrainQueue(slot.regions[static_cast<size_t>(region)]);
}

void Scheduler::DrainQueue(EventQueue& queue) {
  while (!queue.empty()) {
    Event* event = queue.Pop();
    if (event->callback) {
      event->callback();
    }
    pool_.Release(event);
  }
}

}  // namespace delta
