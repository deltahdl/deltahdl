#include "elaborator/semantic_leading_clocks.h"

#include <vector>

#include "elaborator/property_instance.h"
#include "parser/ast.h"

namespace delta {

namespace {

// Whether two clocking events are identical: the same edge over the same
// spelling of the signal. §16.16.1 has two clocks of one value that are
// written differently be not identical.
bool SameClock(const EventExpr& a, const EventExpr& b) {
  if (a.edge != b.edge) return false;
  if (a.signal == nullptr || b.signal == nullptr) {
    return a.signal == b.signal;
  }
  return a.signal->text == b.signal->text && a.signal->kind == b.signal->kind;
}

void AddOnce(std::vector<EventExpr>& set, const EventExpr& ev) {
  for (const EventExpr& have : set) {
    if (SameClock(have, ev)) return;
  }
  set.push_back(ev);
}

void AddAll(std::vector<EventExpr>& set, const std::vector<EventExpr>& add) {
  for (const EventExpr& ev : add) AddOnce(set, ev);
}

// The set with `outer` for the inherited clock, the first event of a clock
// written as a list being the one the operand begins on.
std::vector<EventExpr> Inherited(const std::vector<EventExpr>& outer) {
  std::vector<EventExpr> set;
  if (!outer.empty()) set.push_back(outer[0]);
  return set;
}

std::vector<EventExpr> Clocks(const PropertyExprNode* node,
                              const std::vector<EventExpr>& outer,
                              const PropertyRegistry& registry, int depth);

// The semantic leading clock of a sequence: the clock its first operand is
// written under, else inherited.
std::vector<EventExpr> SequenceClocks(const ModuleItem* seq,
                                      const std::vector<EventExpr>& outer) {
  if (seq != nullptr && !seq->seq_linear.clocks.empty() &&
      !seq->seq_linear.clocks[0].empty()) {
    return Inherited(seq->seq_linear.clocks[0]);
  }
  return Inherited(outer);
}

// An instance of a named property or sequence: the declaration's body, the
// declaration's own clock standing for the inherited one where it has one.
std::vector<EventExpr> InstanceClocks(const Expr* instance,
                                      const std::vector<EventExpr>& outer,
                                      const PropertyRegistry& registry,
                                      int depth) {
  const ModuleItem* seq =
      InstantiatedDecl(instance, ModuleItemKind::kSequenceDecl, registry);
  if (seq != nullptr) {
    return seq->seq_clock.empty() ? SequenceClocks(seq, outer)
                                  : Inherited(seq->seq_clock);
  }
  const ModuleItem* decl =
      InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry);
  if (decl == nullptr || depth >= 4) return Inherited(outer);
  const std::vector<EventExpr>& inner =
      decl->prop_clock.empty() ? outer : decl->prop_clock;
  if (decl->prop_body_tree == nullptr) return Inherited(inner);
  return Clocks(decl->prop_body_tree, inner, registry, depth + 1);
}

std::vector<EventExpr> Clocks(const PropertyExprNode* node,
                              const std::vector<EventExpr>& outer,
                              const PropertyRegistry& registry, int depth) {
  if (node == nullptr) return Inherited(outer);
  // §16.16.1: an operand written under a clocking event of its own has
  // that clock for the inherited one.
  const std::vector<EventExpr>& incoming =
      node->clock.empty() ? outer : node->clock;
  std::vector<EventExpr> set;
  switch (node->kind) {
    case PropertyExprNode::Kind::kSequence:
      return SequenceClocks(node->sequence, incoming);
    case PropertyExprNode::Kind::kBoolean:
      return InstanceClocks(node->boolean, incoming, registry, depth);
    case PropertyExprNode::Kind::kNot:
      if (node->operands.empty()) return Inherited(incoming);
      return Clocks(node->operands[0], incoming, registry, depth);
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd:
      for (const PropertyExprNode* operand : node->operands) {
        AddAll(set, Clocks(operand, incoming, registry, depth));
      }
      return set;
    case PropertyExprNode::Kind::kImplication:
      return SequenceClocks(node->sequence, incoming);
    case PropertyExprNode::Kind::kAbort:
      if (node->synchronous || node->operands.empty()) {
        return Inherited(incoming);
      }
      return Clocks(node->operands[0], incoming, registry, depth);
    default:
      return Inherited(incoming);
  }
}

// Whether every clock in `named` is identical to `clock`.
bool AllIdentical(const std::vector<EventExpr>& named,
                  const std::vector<EventExpr>& clock) {
  for (const EventExpr& ev : named) {
    if (clock.empty() || !SameClock(ev, clock[0])) return false;
  }
  return true;
}

// Whether a sequence's own clock and the clocks on its operands are all
// identical to `clock`.
bool SequenceNamesOnlyClock(const ModuleItem* seq,
                            const std::vector<EventExpr>& clock) {
  if (seq == nullptr) return true;
  if (!AllIdentical(seq->seq_clock, clock)) return false;
  for (const auto& operand_clock : seq->seq_linear.clocks) {
    if (!AllIdentical(operand_clock, clock)) return false;
  }
  return true;
}

// Whether the declaration an instance names, where it names one, is
// clocked by `clock` alone.
bool InstanceNamesOnlyClock(const Expr* instance,
                            const std::vector<EventExpr>& clock,
                            const PropertyRegistry& registry) {
  const ModuleItem* decl =
      InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry);
  if (decl != nullptr && !AllIdentical(decl->prop_clock, clock)) return false;
  return SequenceNamesOnlyClock(
      InstantiatedDecl(instance, ModuleItemKind::kSequenceDecl, registry),
      clock);
}

}  // namespace

std::vector<EventExpr> SemanticLeadingClocks(
    const PropertyExprNode* node, const std::vector<EventExpr>& outer,
    const PropertyRegistry& registry) {
  return Clocks(node, outer, registry, 0);
}

bool HasUniqueSemanticLeadingClock(const PropertyExprNode* node,
                                   const std::vector<EventExpr>& outer,
                                   const PropertyRegistry& registry) {
  return SemanticLeadingClocks(node, outer, registry).size() <= 1;
}

bool TreeNamesOnlyClock(const PropertyExprNode* node,
                        const std::vector<EventExpr>& clock,
                        const PropertyRegistry& registry) {
  if (node == nullptr) return true;
  if (!AllIdentical(node->clock, clock) ||
      !SequenceNamesOnlyClock(node->sequence, clock) ||
      !InstanceNamesOnlyClock(node->boolean, clock, registry)) {
    return false;
  }
  for (const PropertyExprNode* operand : node->operands) {
    if (!TreeNamesOnlyClock(operand, clock, registry)) return false;
  }
  return true;
}

}  // namespace delta
