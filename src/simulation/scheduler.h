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
};

// --- Stratified event scheduler (IEEE 1800-2023 section 4.5) ---

class Scheduler {
 public:
  Scheduler() = default;

  SimTime CurrentTime() const { return current_time_; }
  bool HasEvents() const { return !event_calendar_.empty(); }

  void ScheduleEvent(SimTime time, Region region, Event* event);
  void Run();

 private:
  void ExecuteTimeSlot(TimeSlot& slot);
  void ExecuteActiveRegions(TimeSlot& slot);
  void ExecuteReactiveRegions(TimeSlot& slot);
  void ExecuteRegion(EventQueue& queue);

  bool IterateActiveSet(TimeSlot& slot);
  bool IterateReactiveSet(TimeSlot& slot);
  void RestartActiveSet(TimeSlot& slot);

  std::map<SimTime, TimeSlot> event_calendar_;
  SimTime current_time_{0};
  bool stop_requested_ = false;
};

}  // namespace delta
