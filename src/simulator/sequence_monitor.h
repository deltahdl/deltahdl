#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/instance_bindings.h"
#include "simulator/sequence_flatten.h"

namespace delta {

struct SimCoroutine;
class SimContext;
class Arena;

SimCoroutine MakeSequenceMonitorCoroutine(LinearSequence body,
                                          std::vector<EventExpr> clock,
                                          std::string ep_name, SimContext& ctx,
                                          Arena& arena);

void CollectPastDirectedSites(const Expr* e, std::vector<const Expr*>& sites);
void CollectPastDirectedSites(const LinearSequence& body,
                              std::vector<const Expr*>& sites);

std::string HierarchicalEndPoint(std::string_view path, SimContext& ctx);

struct LinearSequenceAttempt;

enum class SequenceStep : uint8_t { kPending, kMatched, kMatchedLast, kFailed };

LinearSequenceAttempt* NewSequenceAttempt(const LinearSequence& body,
                                          Arena& arena);

SequenceStep StepSequenceAttempt(const LinearSequence& body,
                                 LinearSequenceAttempt& attempt, bool begin,
                                 SimContext& ctx, Arena& arena);

struct SequencePropertyState;

SequencePropertyState* CreateSequencePropertyState(const ModuleItem* seq,
                                                   SimContext& ctx,
                                                   Arena& arena);

enum class SequenceVerdict : uint8_t { kMatched, kFailed, kDisabled };

struct SequenceTick {
  bool disabled = false;
  bool every_match = false;
  std::vector<const InstanceBindings*> instances;
};

struct SequenceOutcome {
  SequenceVerdict verdict = SequenceVerdict::kFailed;
  const InstanceBindings* bindings = nullptr;
  uint64_t started = 0;
};

std::vector<SequenceOutcome> AdvanceSequenceProperty(
    SequencePropertyState& state, const SequenceTick& tick, SimContext& ctx,
    Arena& arena);

std::vector<uint64_t> PendingSequenceStarts(const SequencePropertyState& state);

std::size_t AbortSequencePropertyAttempts(SequencePropertyState& state);

std::size_t AbortSequencePropertyAttemptAt(SequencePropertyState& state,
                                           uint64_t started);

}  // namespace delta
