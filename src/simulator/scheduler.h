#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

class SimContext;
struct Process;

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

struct PendingTimeSlot {
  SimTime time;
  bool before_read_only_synch = false;
};

struct TimeSlot {
  std::array<EventQueue, kRegionCount> regions{};

  bool AnyNonemptyIn(Region first, Region last) const;

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

  SimTime NextEventTime() const {
    if (event_calendar_.empty()) return current_time_;
    auto it = event_calendar_.upper_bound(current_time_);
    if (it == event_calendar_.end()) return current_time_;
    return it->first;
  }

  void NoteThreadSwitch(Process* proc) {
    if (proc == nullptr) return;
    if (threads_seen_.insert(proc).second) threads_.push_back(proc);
  }
  const std::vector<Process*>& Threads() const { return threads_; }
  bool HasRunThread(Process* proc) const {
    return threads_seen_.contains(proc);
  }

  void NoteCarrier(Process* proc) { carriers_.push_back(proc); }
  const std::vector<Process*>& Carriers() const { return carriers_; }

  void PinHandle(uint64_t handle) { ++pinned_handles_[handle]; }
  void UnpinHandle(uint64_t handle) {
    auto it = pinned_handles_.find(handle);
    if (it != pinned_handles_.end() && --it->second == 0) {
      pinned_handles_.erase(it);
    }
  }
  const std::map<uint64_t, uint32_t>& PinnedHandles() const {
    return pinned_handles_;
  }

  void NoteClassObjectMade() { ++class_objects_made_; }
  void NoteClassCollection(size_t live) {
    class_objects_made_ = 0;
    class_collection_due_at_ = live > 0 ? live : 1;
  }
  bool ClassCollectionDue() const {
    return class_objects_made_ >= class_collection_due_at_;
  }

  Region CurrentRegion() const { return current_region_; }
  bool HasEvents() const { return !event_calendar_.empty(); }
  std::vector<PendingTimeSlot> PendingTimeSlots() const;

  void SetContext(SimContext* ctx) { ctx_ = ctx; }

  void ScheduleEvent(SimTime time, Region region, Event* event);
  using NbaCapture = std::vector<std::pair<Event*, Region>>;
  void SetNbaCapture(NbaCapture* capture) { nba_capture_ = capture; }
  void Run();
  void EndSimulation();

  EventPool& GetEventPool() { return pool_; }

  void AddPostTimestepCallback(std::function<void()> cb) {
    post_timestep_cbs_.push_back(std::move(cb));
  }

  void AddTimeSlotStartCallback(std::function<void()> cb) {
    time_slot_start_cbs_.push_back(std::move(cb));
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
  bool Halted() const;
  bool ProgramsEnded() const;
  void ReleaseSlot(TimeSlot& slot);
  void ExecuteTimeSlot(TimeSlot& slot);
  void ExecuteRegion(TimeSlot& slot, Region region);
  void DrainQueue(EventQueue& queue);
  void RunEvent(Event* event);
  void ExecuteIterativeRegion(TimeSlot& slot, Region region, Region home);

  bool IterateActiveSet(TimeSlot& slot);
  bool IterateReactiveSet(TimeSlot& slot);

  EventPool pool_;
  SimContext* ctx_ = nullptr;
  std::map<SimTime, TimeSlot> event_calendar_;
  std::vector<std::function<void()>> post_timestep_cbs_;
  std::vector<std::function<void()>> time_slot_start_cbs_;
  std::vector<Process*> threads_;
  std::unordered_set<Process*> threads_seen_;
  std::vector<Process*> carriers_;
  std::map<uint64_t, uint32_t> pinned_handles_;
  size_t class_objects_made_ = 0;
  size_t class_collection_due_at_ = 1;

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
  NbaCapture* nba_capture_ = nullptr;
};

}  // namespace delta
