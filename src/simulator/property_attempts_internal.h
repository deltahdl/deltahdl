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

// The state of one attempt of a property tree and the algebra of the
// verdicts over it, shared by the tick, in property_attempts.cpp, and the
// end of the run, in property_finish.cpp.

namespace delta {

// The verdict of one operand or of the tree over it: decided true or false,
// or not yet.
enum class Tri : uint8_t { kPending, kTrue, kFalse };

// The flattened sequence of each sequence node of the tree, an antecedent's
// among them, keyed by the node; flattened once for every attempt.
struct FlatSequence {
  const PropertyExprNode* node;
  LinearSequence body;
};

// The state of one node of the tree within one attempt: a leaf's verdict
// once decided and a sequence's attempt while it is in flight; an
// operator's operands' states; and, for an implication, the antecedent's
// attempt with the consequent's states begun at its matches, one to begin
// at the next tick where the implication is nonoverlapped, and whether the
// antecedent can match no more.
struct NodeState {
  Tri verdict = Tri::kPending;
  // §16.14.6.1: the values the instance of a procedural concurrent assertion
  // this attempt is saved when it was queued, bound around every step of the
  // attempt; nullptr for a static assertion's attempt. Set on the root and
  // read there alone.
  const InstanceBindings* bindings = nullptr;
  // §39.4.2: the time the attempt began at, in ticks. Set on the root and
  // read there alone.
  uint64_t started = 0;
  LinearSequenceAttempt* attempt = nullptr;
  // §16.14.3: whether the sequence's attempt, matched at this tick, may
  // match again at a later one.
  bool matches_again = false;
  std::vector<NodeState*> operands;
  std::vector<NodeState*> consequents;
  bool spawn_next = false;
  bool antecedent_done = false;
  // §16.12.6: the condition as read at the attempt's tick.
  bool condition = false;
  // §16.12.10: the ticks a nexttime has still to wait before its operand
  // begins, and whether the operand has begun; §16.12.11: the ticks an
  // always has still to wait before its range, and the ticks of the range
  // at which an operand attempt has still to begin, UINT64_MAX where the
  // range is unbounded.
  uint64_t wait = 0;
  bool begun = false;
  uint64_t remaining = 0;
  // §16.12.12: an until's attempts of its second operand, one begun at each
  // tick beside the first operand's in `consequents`, and the index of the
  // first tick not yet decided in `wait`.
  std::vector<NodeState*> seconds;
  // §16.12.14: an abort's node, so that its condition becoming true between
  // the ticks can be marked on the attempts in flight, and the mark.
  const PropertyExprNode* abort_node = nullptr;
  bool aborted = false;
  // §16.12.16: the index of the case item selected at the attempt's tick,
  // the count of the items where none was.
  size_t selected = 0;
  // §16.12.17: the body a boolean operand that instantiates a named
  // property was expanded to when it began, the actuals substituted, its
  // state the one operand's.
  const PropertyExprNode* expansion = nullptr;
  // §16.13.2: the number of the clock the node is evaluated on, its own or
  // the one flowing to it, and whether it is to begin at that clock's next
  // tick, its parent having begun it at a tick of another.
  int clock = 0;
  bool awaiting = false;
  // §16.10: the variables standing for the locals of the instance the
  // expansion is of, its copies of the property's locals (§16.13.7) and its
  // local variable formal arguments (§16.12.19), each under the name of its
  // own the expressions reading it name, bound in a scope while the
  // expansion steps.
  std::vector<std::pair<std::string_view, Variable*>> locals;
  // §16.12.2: for a sequence, whether it is read as strong, which decides
  // an attempt of it still in flight when the run ends.
  bool strong = false;
};

// §16.13.7: one copy of a local variable of a named property for one
// semantic leading clock of an instance's attempt: the node of the
// expansion it is for, whose subtree reads `reference` in the local's place,
// the variable it names, and the initialization assignment performed to the
// variable at the first tick of that node's clock at or after the attempt
// begins.
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
  // §16.13: the clocks the sequences are evaluated on, the leading clock
  // first, and the time step the tree last advanced at.
  PropertyClocks clocks;
  SimTime advanced_at{PropertyClocks::kNever};
  bool every_match = false;
  // §16.10: how many variables the expansions of the tree's attempts have
  // stood up for their locals, which numbers each one's name.
  uint32_t locals_made = 0;
  // §16.12.2 and F.3.4.3.1: whether the statement the tree is the property
  // of, a cover property or an expect, reads a sequence written with no
  // sequence operator as strong; an assert property and an assume property
  // read one as weak.
  bool plain_sequences_strong = false;
};

// The verdict of an attempt decided, read off its root's state. Defined in
// property_finish.cpp.
PropertyVerdict VerdictOf(const PropertyExprNode* root, const NodeState& state);

// The verdict algebra: not over a verdict, a sequence's step as one, a
// boolean as one, §16.12.4's or and §16.12.5's and over the operands'
// verdicts, and §16.12.8's implies and iff over two.
Tri Not(Tri t);
bool Matched(SequenceStep step);
Tri FromStep(SequenceStep step);
Tri FromBool(bool b);
Tri Junction(bool is_or, const std::vector<Tri>& verdicts);
Tri Implies(Tri first, Tri second);
Tri Iff(Tri first, Tri second);

// §16.12.12: an until decided from its operands' verdicts at the ticks in
// order from the first not yet decided, which `wait` indexes; not yet
// decided where every tick has passed on.
Tri DecideUntil(const PropertyExprNode* node, NodeState& state,
                const std::vector<Tri>& firsts,
                const std::vector<Tri>& seconds);

// The end of the run: a sequence still in flight reads by its strength, an
// antecedent still in flight matches no more, and the rest follows.
Tri Finish(const PropertyExprNode* node, NodeState& state);

// §16.14.8: whether the attempt of `node`, decided, was nonvacuous, defined
// on the structure of the property: a sequence's attempt is nonvacuous
// always, a not's, an instance's, a nexttime's begun and an abort's not
// aborted as its operand's, an or's, an and's and an iff's where either
// operand's is, an if's as the branch its condition took, an implication's
// where a consequent begun at an end point of the antecedent is, an
// implies' where the first operand held and the second's is, an always's,
// an eventually's and an until's where a tick's operand attempt is with
// the ticks before it holding, not holding or, for an until, the first
// holding and the second not, and a case's as the item it selected. Defined
// in property_vacuity.cpp.
bool Nonvacuous(const PropertyExprNode* node, const NodeState& state);

}  // namespace delta
