#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <set>
#include <string>
#include <string_view>
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

constexpr int kCoverageTypeFsmTransition = 24;

template <typename Item>
struct CoverageInstanceItems {
  std::string scope;
  std::uint64_t resets = 0;
  std::int64_t covered = 0;
  std::vector<Item*> items;
};

struct StatementTally {
  const Stmt* stmt = nullptr;
  std::string prefix;
  CoverageInstanceItems<StatementTally>* instance = nullptr;
  std::uint64_t executions = 0;
};

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

struct AssertionTally {
  const Stmt* stmt = nullptr;
  std::string prefix;
  CoverageInstanceItems<AssertionTally>* instance = nullptr;
  std::string key;
  AssertionCoverageCounters counts;
};

struct AssertionCoverageOverride {
  bool collecting = true;
  std::uint64_t epoch = 0;
};

struct FsmCount {
  FsmDecl decl;
  std::vector<Variable*> signals;
  std::optional<std::pair<int64_t, int64_t>> select;
  std::vector<std::pair<std::string_view, uint64_t>> states;
  std::unordered_map<uint64_t, std::uint64_t> visits;
  std::optional<uint64_t> last;
  std::set<std::pair<uint64_t, uint64_t>> transitions;
};

struct InstanceFsms {
  std::string prefix;
  std::string scope;
  std::vector<FsmCount> fsms;
  std::uint64_t state_resets = 0;
  std::uint64_t transition_resets = 0;
};

struct FsmHandleRef {
  InstanceFsms* instance = nullptr;
  std::size_t fsm = 0;
  std::optional<uint64_t> state;
  VpiObject* state_expression = nullptr;
};

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

template <typename Tally>
Tally* TallyIn(const std::unordered_map<const Stmt*, std::vector<Tally*>>& map,
               const Stmt* stmt, const std::string& prefix) {
  auto found = map.find(stmt);
  if (found == map.end()) return nullptr;
  auto held = std::ranges::find(found->second, prefix, &Tally::prefix);
  return held == found->second.end() ? nullptr : *held;
}

std::string CoverageInstancePrefix(std::string prefix);

void AttachCodeCoverage(const RtlirDesign* design, SimContext& ctx);

}  // namespace delta
