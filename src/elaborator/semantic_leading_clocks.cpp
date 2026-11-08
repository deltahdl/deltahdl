#include "elaborator/semantic_leading_clocks.h"

#include <vector>

#include "elaborator/property_instance.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

bool SameClock(const EventExpr& a, const EventExpr& b) {
  if (a.edge != b.edge) return false;
  if (a.signal == nullptr || b.signal == nullptr) {
    return a.signal == b.signal;
  }
  return SamePath(a.signal, b.signal);
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

std::vector<EventExpr> Inherited(const std::vector<EventExpr>& outer) {
  std::vector<EventExpr> set;
  if (!outer.empty()) set.push_back(outer[0]);
  return set;
}

std::vector<EventExpr> Clocks(const PropertyExprNode* node,
                              const std::vector<EventExpr>& outer,
                              const PropertyRegistry& registry, int depth);

std::vector<EventExpr> InstanceClocks(const Expr* instance,
                                      const std::vector<EventExpr>& outer,
                                      const PropertyRegistry& registry,
                                      int depth);

std::vector<EventExpr> ChainClocks(const SeqLinearBody& body,
                                   const std::vector<EventExpr>& outer,
                                   const PropertyRegistry& registry,
                                   int depth) {
  std::vector<EventExpr> set;
  if (!body.clocks.empty() && !body.clocks[0].empty()) {
    set = Inherited(body.clocks[0]);
  } else if (!body.operands.empty() && depth < 4 &&
             InstantiatedDecl(body.operands[0], ModuleItemKind::kSequenceDecl,
                              registry) != nullptr) {
    set = InstanceClocks(body.operands[0], outer, registry, depth + 1);
  } else {
    set = Inherited(outer);
  }
  for (const auto* chains : {&body.conjuncts, &body.alternatives}) {
    for (const SeqLinearBody& chain : *chains) {
      AddAll(set, ChainClocks(chain, set, registry, depth));
    }
  }
  return set;
}

std::vector<EventExpr> SequenceClocks(const ModuleItem* seq,
                                      const std::vector<EventExpr>& outer,
                                      const PropertyRegistry& registry,
                                      int depth) {
  if (seq == nullptr) return Inherited(outer);
  if (!seq->seq_clock.empty()) return Inherited(seq->seq_clock);
  return ChainClocks(seq->seq_linear, outer, registry, depth);
}

std::vector<EventExpr> InstanceClocks(const Expr* instance,
                                      const std::vector<EventExpr>& outer,
                                      const PropertyRegistry& registry,
                                      int depth) {
  const ModuleItem* seq =
      InstantiatedDecl(instance, ModuleItemKind::kSequenceDecl, registry);
  if (seq != nullptr) return SequenceClocks(seq, outer, registry, depth);
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
  const std::vector<EventExpr>& incoming =
      node->clock.empty() ? outer : node->clock;
  std::vector<EventExpr> set;
  switch (node->kind) {
    case PropertyExprNode::Kind::kSequence:
      return SequenceClocks(node->sequence, incoming, registry, depth);
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
      return SequenceClocks(node->sequence, incoming, registry, depth);
    case PropertyExprNode::Kind::kAbort:
      if (node->synchronous || node->operands.empty()) {
        return Inherited(incoming);
      }
      return Clocks(node->operands[0], incoming, registry, depth);
    default:
      return Inherited(incoming);
  }
}

bool AllIdentical(const std::vector<EventExpr>& named,
                  const std::vector<EventExpr>& clock) {
  for (const EventExpr& ev : named) {
    if (clock.empty() || !SameClock(ev, clock[0])) return false;
  }
  return true;
}

bool SequenceNamesOnlyClock(const ModuleItem* seq,
                            const std::vector<EventExpr>& clock) {
  if (seq == nullptr) return true;
  if (!AllIdentical(seq->seq_clock, clock)) return false;
  for (const auto& operand_clock : seq->seq_linear.clocks) {
    if (!AllIdentical(operand_clock, clock)) return false;
  }
  return true;
}

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

static const EventExpr& InheritedPlaceholder() {
  static const Expr kName = [] {
    Expr name;
    name.kind = ExprKind::kIdentifier;
    name.text = "$inherited";
    return name;
  }();
  static const EventExpr kEvent = [] {
    EventExpr ev;
    ev.signal = const_cast<Expr*>(&kName);
    return ev;
  }();
  return kEvent;
}

std::vector<EventExpr> DeterminedLeadingClock(
    const PropertyExprNode* node, const PropertyRegistry& registry) {
  std::vector<EventExpr> set =
      Clocks(node, {InheritedPlaceholder()}, registry, 0);
  if (set.size() != 1 || set[0].signal == InheritedPlaceholder().signal) {
    return {};
  }
  return set;
}

std::vector<EventExpr> DeterminedSequenceClock(
    const ModuleItem* seq, const PropertyRegistry& registry) {
  std::vector<EventExpr> set =
      SequenceClocks(seq, {InheritedPlaceholder()}, registry, 0);
  if (set.size() != 1 || set[0].signal == InheritedPlaceholder().signal) {
    return {};
  }
  return set;
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
