#pragma once

// IEEE 1800-2023 §40.2.1 and §40.2.2: the coverage a run collects of the
// types the API supports at a minimum - statements, toggles, FSM states and
// transitions, and assertions - kept item by item. The coverage-control state
// (coverage_control.h) holds one instance's figure of each type, which is what
// the §40.3.2 functions read; this is what that figure is counted from, and
// what §40.5.2's vpi_get() reads one statement, one signal, one assertion, one
// FSM or one FSM state out of.

#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_fsm.h"
#include "simulator/vpi_coverage.h"

namespace delta {

struct RtlirDesign;
struct Stmt;
struct Variable;
struct VpiObject;
class CoverageControlState;
class SimContext;

// §40.2.1 c) lets a tool add coverage types, and §40.2.1 b) lists FSM
// transitions beside FSM states among those it supports at a minimum while
// §40.3.1 gives them no constant of their own. This is the type value the
// §40.3.2 functions read deltahdl's transition coverage under: the number of
// distinct moves from one legal state to another each FSM has made, out of
// every ordered pair of two different legal states.
constexpr int kCoverageTypeFsmTransition = 24;

// The items of one coverage type one instance holds: the instance's scope in
// the coverage-control state, the resets of that type in the scope already
// applied to the items, how many of them are covered, and the items.
template <typename Item>
struct CoverageInstanceItems {
  std::string scope;
  std::uint64_t resets = 0;
  std::int64_t covered = 0;
  std::vector<Item*> items;
};

// §40.2.2 statement coverage: one statement of one instance, and how many
// times it has executed there while the instance collected.
struct StatementTally {
  const Stmt* stmt = nullptr;
  // The instance's key, as a running process names the instance it stands
  // in, with no trailing dot.
  std::string prefix;
  CoverageInstanceItems<StatementTally>* instance = nullptr;
  std::uint64_t executions = 0;
};

// §40.2.2 toggle coverage: the bits of one signal of one instance, which of
// them have held a 0 and which a 1 while the instance collected, and how many
// times each has moved between the two. `next` is the record of the same
// variable in another instance, one a port connection shares it with.
struct ToggleSignal {
  Variable* var = nullptr;
  CoverageInstanceItems<ToggleSignal>* instance = nullptr;
  CoverageControlState* coverage = nullptr;
  std::vector<std::uint64_t> seen0;
  std::vector<std::uint64_t> seen1;
  std::vector<Logic4Word> last;
  std::vector<std::uint64_t> toggles;
  ToggleSignal* next = nullptr;
};

// §40.2.2 assertion coverage with §40.5.2's tallies: one assertion of one
// instance. `key` is the name the assertion API keeps it under (§39), which
// an assertion handle is matched by, recorded at its first attempt.
struct AssertionTally {
  const Stmt* stmt = nullptr;
  std::string prefix;
  CoverageInstanceItems<AssertionTally>* instance = nullptr;
  std::string key;
  AssertionCoverageCounters counts;
};

// §40.5.3: a start or a stop vpi_control() applied to one assertion through
// its handle. It holds until its instance's collection of assertion coverage
// next changes, the instance's starts and stops numbering `epoch` when it was
// applied.
struct AssertionCoverageOverride {
  bool collecting = true;
  std::uint64_t epoch = 0;
};

// §40.4: one FSM of one instance, as its pragmas declare it: the signals
// holding its current state, the bits of the one signal a part-select holds
// it in, and its legal states, each the value of a parameter, by name in
// declaration order. §40.2.2 counts the states it reaches, and §40.5.2 the
// times it enters each; §40.2.1 adds the distinct moves between two of them.
struct FsmCount {
  FsmDecl decl;
  std::vector<Variable*> signals;
  std::optional<std::pair<int64_t, int64_t>> select;  // low and high offset
  std::vector<std::pair<std::string_view, uint64_t>> states;
  std::unordered_map<uint64_t, std::uint64_t> visits;
  std::optional<uint64_t> last;
  std::set<std::pair<uint64_t, uint64_t>> transitions;
};

// The FSMs of one instance, counted together as the instance's coverage, and
// the resets of either FSM coverage type already applied to their counts.
struct InstanceFsms {
  std::string prefix;
  std::string scope;
  std::vector<FsmCount> fsms;
  std::uint64_t state_resets = 0;
  std::uint64_t transition_resets = 0;
};

// §40.5.1 and §40.5.2: what an FSM handle or an FSM state handle stands for,
// one FSM of one instance or one legal state of it, and, for an FSM, the
// object of the signal or expression holding its state.
struct FsmHandleRef {
  InstanceFsms* instance = nullptr;
  std::size_t fsm = 0;
  std::optional<uint64_t> state;
  VpiObject* state_expression = nullptr;
};

// Everything the run collects, item by item. Records are held where adding
// one never moves another, since each is reached by pointer: a statement and
// an assertion by the statement it is, a signal by its variable, and an FSM or
// a state by its handle.
struct CodeCoverage {
  std::deque<CoverageInstanceItems<StatementTally>> statement_instances;
  std::deque<StatementTally> statement_tallies;
  std::unordered_map<const Stmt*, std::vector<StatementTally*>> statements;

  std::deque<CoverageInstanceItems<ToggleSignal>> toggle_instances;
  std::deque<ToggleSignal> toggle_signals;
  std::unordered_map<const Variable*, ToggleSignal*> toggles;

  std::deque<CoverageInstanceItems<AssertionTally>> assertion_instances;
  std::deque<AssertionTally> assertion_tallies;
  std::unordered_map<const Stmt*, std::vector<AssertionTally*>> assertions;
  std::unordered_map<std::string, AssertionCoverageOverride>
      assertion_overrides;

  std::deque<InstanceFsms> fsm_instances;
  std::unordered_map<const VpiObject*, FsmHandleRef> fsm_handles;
};

// The tally of `stmt` in the instance keyed `prefix` among `tallies`; null
// where it has none there.
template <typename Tally>
Tally* TallyIn(const std::unordered_map<const Stmt*, std::vector<Tally*>>& map,
               const Stmt* stmt, const std::string& prefix) {
  auto found = map.find(stmt);
  if (found == map.end()) return nullptr;
  for (Tally* tally : found->second) {
    if (tally->prefix == prefix) return tally;
  }
  return nullptr;
}

// The instance key a running process names its instance by, without the
// trailing dot it carries.
std::string CoverageInstancePrefix(std::string prefix);

// §40.2.2: arm the collection of statement, toggle, FSM and assertion
// coverage over every instance of `design`, each instance holding items of a
// type being given them as its coverable items, full availability and
// collection started, as §40.3.2.1 has coverage start with the simulation.
void AttachCodeCoverage(const RtlirDesign* design, SimContext& ctx);

}  // namespace delta
