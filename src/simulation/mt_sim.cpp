#include "simulation/mt_sim.h"

#include <algorithm>
#include <cstdint>
#include <string_view>
#include <thread>
#include <utility>
#include <vector>

#include "simulation/compiled_sim.h"
#include "simulation/sim_context.h"

namespace delta {

namespace {

bool SignalInList(std::string_view sig,
                  const std::vector<std::string_view>& list) {
  return std::find(list.begin(), list.end(), sig) != list.end();
}

bool WritesConflictWith(const std::vector<std::string_view>& writes,
                        const SignalDep& other) {
  for (const auto& w : writes) {
    if (SignalInList(w, other.reads)) return true;
    if (SignalInList(w, other.writes)) return true;
  }
  return false;
}

}  // namespace

// =============================================================================
// Partitioner
// =============================================================================

void Partitioner::AddDependency(const SignalDep& dep) { deps_.push_back(dep); }

std::vector<SimPartition> Partitioner::BuildPartitions() const {
  std::vector<SimPartition> partitions;
  std::vector<bool> assigned(deps_.size(), false);
  uint32_t partition_id = 0;

  for (size_t i = 0; i < deps_.size(); ++i) {
    if (assigned[i]) continue;
    SimPartition part;
    part.id = partition_id++;
    part.process_ids.push_back(deps_[i].process_id);
    assigned[i] = true;

    std::vector<size_t> member_indices = {i};
    AddNonConflicting(part, assigned, i, member_indices);
    partitions.push_back(std::move(part));
  }
  return partitions;
}

void Partitioner::AddNonConflicting(SimPartition& part,
                                    std::vector<bool>& assigned, size_t start,
                                    std::vector<size_t>& members) const {
  for (size_t j = start + 1; j < deps_.size(); ++j) {
    if (assigned[j]) continue;
    if (ConflictsWithAny(deps_[j], members)) continue;
    part.process_ids.push_back(deps_[j].process_id);
    assigned[j] = true;
    members.push_back(j);
  }
}

bool Partitioner::ConflictsWithAny(const SignalDep& candidate,
                                   const std::vector<size_t>& members) const {
  for (size_t idx : members) {
    if (HasConflict(deps_[idx], candidate)) return true;
  }
  return false;
}

bool Partitioner::HasConflict(const SignalDep& a, const SignalDep& b) const {
  if (WritesConflictWith(a.writes, b)) return true;
  if (WritesConflictWith(b.writes, a)) return true;
  return false;
}

// =============================================================================
// MtScheduler
// =============================================================================

MtScheduler::MtScheduler(uint32_t num_threads) : num_threads_(num_threads) {}

void MtScheduler::SetPartitions(std::vector<SimPartition> partitions) {
  partitions_ = std::move(partitions);
}

void MtScheduler::RunTimestep(SimContext& ctx,
                              const std::vector<CompiledProcess>& processes) {
  if (partitions_.empty()) return;

  auto execute_partition = [&ctx, &processes](const SimPartition& part) {
    for (uint32_t pid : part.process_ids) {
      for (const auto& proc : processes) {
        if (proc.Id() == pid) {
          proc.Execute(ctx);
          break;
        }
      }
    }
  };

  if (partitions_.size() == 1 || num_threads_ <= 1) {
    for (const auto& part : partitions_) {
      execute_partition(part);
    }
    return;
  }

  // Multi-threaded: launch one thread per partition.
  std::vector<std::jthread> threads;
  threads.reserve(partitions_.size());
  for (const auto& part : partitions_) {
    threads.emplace_back(
        [&execute_partition, &part]() { execute_partition(part); });
  }
  // jthreads auto-join on destruction.
}

}  // namespace delta
