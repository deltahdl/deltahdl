#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "simulator/instance_bindings.h"

namespace delta {

struct Expr;
struct Process;
class SimContext;
struct Stmt;

struct ProceduralAssertionState {
  const Stmt* stmt = nullptr;
  Process* monitor = nullptr;
  std::vector<const InstanceBindings*> pending;
  std::vector<const InstanceBindings*> matured;
  bool maturing_scheduled = false;
  bool reached = false;
  uint64_t ticked_at = ~static_cast<uint64_t>(0);
  std::vector<std::string_view> named_scopes;
};

struct ProceduralCheckerAssertion {
  const Stmt* stmt = nullptr;
  ProceduralAssertionState* state = nullptr;
  std::string inst_prefix;
  std::vector<const Expr*> saved_actuals;
};

const ProceduralCheckerAssertion* StartProceduralCheckerAssertion(
    const Stmt* stmt, std::string_view inst_prefix,
    std::vector<const Expr*> saved_actuals, SimContext& ctx, Arena& arena);

void EnqueueProceduralCheckerAssertion(
    const ProceduralCheckerAssertion& assertion, SimContext& ctx, Arena& arena);

void StartProceduralAssertionMonitors(Process* proc, const Stmt* body,
                                      SimContext& ctx, Arena& arena);

bool EnqueueProceduralAssertion(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

void FlushProceduralAssertionQueue(Process& proc);

bool DisableProceduralAssertion(Process& proc, std::string_view label);

}  // namespace delta
