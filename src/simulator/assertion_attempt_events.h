#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/property_attempts.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sampling.h"

// What the events of one attempt of an assertion statement reach as the run
// evaluates it: the results §16.14.3 keeps of a concurrent cover, and the
// callbacks §39.4.2 has an application place on the assertion.

namespace delta {

// §39.3.1: the key the assertion API keeps `stmt` under as it runs in the
// scope named `scope`: AssertionKey over that scope and the statement's
// label, or, where it has none, the place it starts at as it was written.
std::string RunAssertionKey(const Stmt* stmt, std::string_view scope,
                            SimContext& ctx);

// An attempt of `stmt` begun at the current time: §16.14.3 counts it in a
// concurrent cover's results, and §39.4.2 calls each cbAssertionStart
// callback placed on the assertion.
void NoteAttemptBegun(const Stmt* stmt, SimContext& ctx);

// The verdict an attempt of `stmt` reached at the current time: §16.14.3
// counts a cover's success in its results, and §39.4.2 calls each
// cbAssertionSuccess, cbAssertionVacuousSuccess or cbAssertionFailure
// callback placed on the assertion, as the verdict is, handed the time the
// attempt began at.
void NoteAttemptVerdict(const Stmt* stmt, const PropertyVerdict& verdict,
                        SimContext& ctx);

// §39.4.2: an attempt of `stmt` begun at `started`, in ticks, that the
// disable condition drops at the current time calls each
// cbAssertionDisabledEvaluation callback placed on the assertion.
void NoteAttemptDisabled(const Stmt* stmt, uint64_t started, SimContext& ctx);

// §39.4.2: calls each `reason` control callback placed on the assertion the
// API keeps under `key`, with the current time as cb_time: at once, or,
// §39.4.2.1, for an assertion whose property names a global clocking future
// sampled value function (§16.9.4), at the nearest tick of its global clocking
// event after the current time.
void RaiseAssertionControlCallback(std::string_view key, int reason,
                                   SimContext& ctx);

using OperandRead = AssertionSampleStore::OperandRead;
// What one attempt read at one tick, led by the note of its step.
using AttemptLog = std::vector<const OperandRead*>;

// §39.4.2: the operands the attempts of the assertion `stmt` read at one
// tick, logged on the run's samples from construction to Finish where a
// callback is placed, and only there, so that a run no application watches
// pays nothing for them.
class AttemptReads {
 public:
  AttemptReads(const Stmt* stmt, SimContext& ctx);
  ~AttemptReads();
  AttemptReads(const AttemptReads&) = delete;
  AttemptReads& operator=(const AttemptReads&) = delete;

  // The tick is over, `decided` the verdicts its attempts reached: each
  // failure is given the expression it failed at -- the last operand the
  // attempt read false at the tick, else the last it read -- and, §39.5.2,
  // each attempt that steps calls its step callbacks, a failing step where
  // it failed and a succeeding one otherwise, with the operands it matched
  // at the tick, the failing one last, and the states it went from and to:
  // the origin, 0, before its first step, the accepting state, 1, after a
  // step to success, and the k-th step's own state, k + 1, otherwise.
  void Finish(std::vector<PropertyVerdict>& decided);

 private:
  // §39.5.2: the step callbacks of the attempt that read `reads`, where it
  // steps, `verdict` what it reached at the tick, null where it reached
  // none, and `failed` the operand it failed at.
  void Step(const AttemptLog& reads, const PropertyVerdict* verdict,
            const OperandRead* failed);

  const Stmt* stmt_;
  SimContext& ctx_;
  bool logging_ = false;
  std::vector<OperandRead> log_;
};

}  // namespace delta
