#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

namespace delta {

struct Process;

// =============================================================================
// SimPartition: a subset of processes that share no signals
// =============================================================================

struct SimPartition {
  uint32_t id = 0;
  std::vector<uint32_t> process_ids;
};

// =============================================================================
// SignalDep: describes a process's signal dependencies
// =============================================================================

struct SignalDep {
  uint32_t process_id = 0;
  std::vector<std::string_view> reads;
  std::vector<std::string_view> writes;
};

// =============================================================================
// Partitioner: builds partitions from the signal dependency graph
// =============================================================================

class Partitioner {
 public:
  void AddDependency(const SignalDep& dep);
  std::vector<SimPartition> BuildPartitions() const;
  uint32_t ProcessCount() const { return static_cast<uint32_t>(deps_.size()); }

 private:
  bool HasConflict(const SignalDep& a, const SignalDep& b) const;
  bool ConflictsWithAny(const SignalDep& candidate,
                        const std::vector<size_t>& members) const;
  void AddNonConflicting(SimPartition& part, std::vector<bool>& assigned,
                         size_t start, std::vector<size_t>& members) const;

  std::vector<SignalDep> deps_;
};

// =============================================================================
// MtScheduler: runs partitions in parallel using a thread pool
// =============================================================================

class MtScheduler {
 public:
  explicit MtScheduler(uint32_t num_threads);

  void SetPartitions(std::vector<SimPartition> partitions);
  uint32_t NumPartitions() const {
    return static_cast<uint32_t>(partitions_.size());
  }
  uint32_t NumThreads() const { return num_threads_; }
  const std::vector<SimPartition>& Partitions() const { return partitions_; }

 private:
  uint32_t num_threads_;
  std::vector<SimPartition> partitions_;
};

}  // namespace delta
