#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/property_attempts.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

struct Process;

std::string RunAssertionKey(const Stmt* stmt, std::string_view scope,
                            SimContext& ctx);

void NoteAttemptBegun(const Stmt* stmt, SimContext& ctx);

void NoteAttemptVerdict(const Stmt* stmt, const PropertyVerdict& verdict,
                        SimContext& ctx);

void NoteAttemptDisabled(const Stmt* stmt, uint64_t started, SimContext& ctx);

void NoteAttemptsKilled(const Stmt* stmt, const Process& proc,
                        std::size_t killed, SimContext& ctx);

void RaiseAssertionControlCallback(std::string_view key, int reason,
                                   SimContext& ctx);

using OperandRead = AssertionSampleStore::OperandRead;
using AttemptLog = std::vector<const OperandRead*>;

class AttemptReads {
 public:
  AttemptReads(const Stmt* stmt, SimContext& ctx);
  ~AttemptReads();
  AttemptReads(const AttemptReads&) = delete;
  AttemptReads& operator=(const AttemptReads&) = delete;

  void Finish(std::vector<PropertyVerdict>& decided);

 private:
  void Step(const AttemptLog& reads, const PropertyVerdict* verdict,
            const OperandRead* failed);

  const Stmt* stmt_;
  SimContext& ctx_;
  bool logging_ = false;
  std::vector<OperandRead> log_;
};

}  // namespace delta
