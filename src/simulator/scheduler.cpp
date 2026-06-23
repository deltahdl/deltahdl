#include "simulator/scheduler.h"

#include <cstdio>
#include <cstdlib>

#include "common/arena.h"

namespace delta {

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
  event->superseded = nullptr;
  event->next = free_list_;
  free_list_ = event;
  ++free_count_;
}

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

void Scheduler::ScheduleEvent(SimTime time, Region region, Event* event) {
  if (time < current_time_) {
    std::fprintf(
        stderr,
        "scheduler: refusing to schedule event at past time %llu "
        "(current=%llu); §4.4 ¶2 forbids backwards-in-time scheduling\n",
        static_cast<unsigned long long>(time.ticks),
        static_cast<unsigned long long>(current_time_.ticks));
    std::abort();
  }

  if (event->kind == EventKind::kPli && region == Region::kObserved) {
    ++illegal_observed_pli_count_;
    pool_.Release(event);
    return;
  }

  if (current_region_ == Region::kPreponed && time == current_time_ &&
      region != Region::kPreponed) {
    ++illegal_preponed_schedule_count_;
  }

  if (current_region_ == Region::kPostponed && time == current_time_ &&
      region != Region::kPostponed) {
    ++illegal_postponed_schedule_count_;
  }

  // §4.4.3.5: the Pre-Observed region only lets PLI routines read the
  // stabilized active region set; scheduling any event into the current time
  // slot from within it is illegal.
  if (current_region_ == Region::kPreObserved && time == current_time_) {
    ++illegal_pre_observed_schedule_count_;
  }

  if (event->kind == EventKind::kUpdate) {
    ++update_events_scheduled_count_;
  } else {
    ++evaluation_events_scheduled_count_;
  }
  auto idx = static_cast<size_t>(region);
  event_calendar_[time].regions[idx].Push(event);
}

static bool SlotHasLiveEvent(const TimeSlot& slot) {
  for (const auto& queue : slot.regions) {
    for (const Event* e = queue.head; e; e = e->next) {
      if (!e->superseded || !*e->superseded) return true;
    }
  }
  return false;
}

void Scheduler::Run() {
  while (!event_calendar_.empty() && !stop_requested_) {
    auto it = event_calendar_.begin();
    if (!SlotHasLiveEvent(it->second)) {
      // Every event here is a superseded inertial-delay timeout that an earlier
      // operand change cancelled (IEEE 1800 §28). They do no work, so drop them
      // without advancing simulation time past the last real activity.
      for (auto& queue : it->second.regions) {
        while (!queue.empty()) pool_.Release(queue.Pop());
      }
      event_calendar_.erase(it);
      continue;
    }
    current_time_ = it->first;
    ExecuteTimeSlot(it->second);
    event_calendar_.erase(it);
  }
}

void Scheduler::ExecuteTimeSlot(TimeSlot& slot) {
  ExecuteRegion(slot, Region::kPreponed);

  ExecuteRegion(slot, Region::kPreActive);

  while (slot.AnyIterativeNonempty()) {
    while (IterateActiveSet(slot)) {
    }
    while (IterateReactiveSet(slot)) {
    }

    if (!slot.AnyNonemptyIn(Region::kActive, Region::kPostReNBA)) {
      ExecuteRegion(slot, Region::kPrePostponed);
    }
  }

  ExecuteRegion(slot, Region::kPostponed);

  current_region_ = Region::kCOUNT;
  if (post_timestep_cb_) post_timestep_cb_();
}

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
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsActiveRegionSet(r) || r == Region::kPreObserved ||
        r == Region::kObserved || r == Region::kPostObserved) {
      ExecuteRegion(slot, r);
    }
  }
}

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
  for (size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    if (IsReactiveRegionSet(r)) {
      ExecuteRegion(slot, r);
    }
  }
}

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
