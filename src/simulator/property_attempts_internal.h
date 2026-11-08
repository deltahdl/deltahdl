#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/instance_bindings.h"
#include "simulator/property_attempts.h"
#include "simulator/property_clocks.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_monitor.h"
#include "simulator/variable.h"

namespace delta {

enum class Tri : uint8_t { kPending, kTrue, kFalse };

struct FlatSequence {
  const PropertyExprNode* node;
  LinearSequence body;
};

struct NodeState {
  Tri verdict = Tri::kPending;
  const InstanceBindings* bindings = nullptr;
  uint64_t started = 0;
  LinearSequenceAttempt* attempt = nullptr;
  bool matches_again = false;
  std::vector<NodeState*> operands;
  std::vector<NodeState*> consequents;
  bool spawn_next = false;
  bool antecedent_done = false;
  bool condition = false;
  uint64_t wait = 0;
  bool begun = false;
  uint64_t remaining = 0;
  std::vector<NodeState*> seconds;
  const PropertyExprNode* abort_node = nullptr;
  bool aborted = false;
  size_t selected = 0;
  const PropertyExprNode* expansion = nullptr;
  int clock = 0;
  bool awaiting = false;
  std::vector<std::pair<std::string_view, Variable*>> locals;
  bool strong = false;
};

struct LocalCopy {
  const PropertyExprNode* node;
  std::string_view name;
  Expr* reference;
  const Expr* init;
  Variable* var;
};

struct PropertyTreeState {
  const PropertyExprNode* root = nullptr;
  std::vector<FlatSequence> sequences;
  std::vector<const Expr*> past_sites;
  std::vector<NodeState*> attempts;
  std::vector<LocalCopy> local_copies;
  PropertyClocks clocks;
  SimTime advanced_at{PropertyClocks::kNever};
  bool every_match = false;
  uint32_t locals_made = 0;
  bool plain_sequences_strong = false;
};

PropertyVerdict VerdictOf(const PropertyExprNode* root, const NodeState& state);

Tri Not(Tri t);
bool Matched(SequenceStep step);
Tri FromStep(SequenceStep step);
Tri FromBool(bool b);
Tri Junction(bool is_or, const std::vector<Tri>& verdicts);
Tri Implies(Tri first, Tri second);
Tri Iff(Tri first, Tri second);

Tri DecideUntil(const PropertyExprNode* node, NodeState& state,
                const std::vector<Tri>& firsts,
                const std::vector<Tri>& seconds);

Tri Finish(const PropertyExprNode* node, NodeState& state);

bool Nonvacuous(const PropertyExprNode* node, const NodeState& state);

}  // namespace delta
