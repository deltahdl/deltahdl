#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

using SequenceMap = std::unordered_map<std::string_view, const ModuleItem*>;
using Clock = std::vector<EventExpr>;

// Each expression of the sequence body `body` and of the bodies nested in
// it, handed to `fn`.
template <typename Fn>
void ForEachBodyExpr(const SeqLinearBody& body, const Fn& fn) {
  for (const Expr* operand : body.operands) fn(operand);
  for (const auto& items : body.match_items) {
    for (const SeqMatchAssign& item : items) {
      fn(item.rhs);
      fn(item.call);
    }
  }
  for (const SeqThroughout& guard : body.throughouts) fn(guard.cond);
  for (const auto* nested :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (const SeqLinearBody& inner : *nested) ForEachBodyExpr(inner, fn);
  }
}

// Each expression of the property tree under `node`, handed to `fn`.
template <typename Fn>
void ForEachTreeExpr(const PropertyExprNode* node, const Fn& fn) {
  if (node == nullptr) return;
  fn(node->boolean);
  if (node->sequence != nullptr)
    ForEachBodyExpr(node->sequence->seq_linear, fn);
  for (const PropertyExprNode* operand : node->operands) {
    ForEachTreeExpr(operand, fn);
  }
}

template <typename Pred>
bool ExprAny(const Expr* e, const Pred& pred) {
  if (e == nullptr) return false;
  return pred(e) || AnyExprChild(e, [&](const Expr* child) {
           return ExprAny(child, pred);
         });
}

// The named sequence `e` instantiates, written as a call or a bare name.
const ModuleItem* InstanceOf(const Expr* e, const SequenceMap& sequences) {
  if (e == nullptr) return nullptr;
  std::string_view name = e->kind == ExprKind::kCall         ? e->callee
                          : e->kind == ExprKind::kIdentifier ? e->text
                                                             : "";
  auto it = sequences.find(name);
  return it == sequences.end() ? nullptr : it->second;
}

// The named sequence `e` applies triggered to, null where it applies none.
const ModuleItem* TriggeredSequence(const Expr* e,
                                    const SequenceMap& sequences) {
  if (e->kind != ExprKind::kMemberAccess || e->rhs == nullptr ||
      e->rhs->text != "triggered") {
    return nullptr;
  }
  return InstanceOf(e->lhs, sequences);
}

bool BodyHasMatchItems(const SeqLinearBody& body, const SequenceMap& sequences,
                       std::unordered_set<const ModuleItem*>& seen);

// Whether `e` instantiates a named sequence whose body has a match item.
bool InstantiatesMatchItems(const Expr* e, const SequenceMap& sequences,
                            std::unordered_set<const ModuleItem*>& seen) {
  return ExprAny(e, [&](const Expr* sub) {
    const ModuleItem* seq = InstanceOf(sub, sequences);
    return seq != nullptr && seen.insert(seq).second &&
           BodyHasMatchItems(seq->seq_linear, sequences, seen);
  });
}

// Whether `body` holds a sequence match item, its own or one of a sequence
// it instantiates; `seen` holds the sequences already followed.
bool BodyHasMatchItems(const SeqLinearBody& body, const SequenceMap& sequences,
                       std::unordered_set<const ModuleItem*>& seen) {
  bool found = !body.first_match_items.empty();
  for (const auto& items : body.match_items) found = found || !items.empty();
  ForEachBodyExpr(body, [&](const Expr* e) {
    found = found || InstantiatesMatchItems(e, sequences, seen);
  });
  return found;
}

bool IsFutureGclk(const Expr* e) {
  GlobalClockingSampledFunction fn{};
  return e->kind == ExprKind::kSystemCall &&
         ClassifyGlobalClockingSampledFunction(e->callee, fn) &&
         IsGlobalClockingFutureFunction(fn);
}

bool TreeHasMatchItems(const PropertyExprNode* node,
                       const SequenceMap& sequences,
                       std::unordered_set<const ModuleItem*>& seen) {
  if (node == nullptr) return false;
  if ((node->sequence != nullptr &&
       BodyHasMatchItems(node->sequence->seq_linear, sequences, seen)) ||
      InstantiatesMatchItems(node->boolean, sequences, seen)) {
    return true;
  }
  for (const PropertyExprNode* operand : node->operands) {
    if (TreeHasMatchItems(operand, sequences, seen)) return true;
  }
  return false;
}

// §16.9.4: a global clocking future sampled value function stands in no
// assertion holding a sequence match item, its own or one reached through
// an instance of a named sequence.
void CheckFutureGclkWithMatchItems(const Stmt* s, const SequenceMap& sequences,
                                   DiagEngine& diag) {
  bool future = false;
  auto visit = [&](const Expr* e) {
    future = future || ExprAny(e, IsFutureGclk);
  };
  ForEachTreeExpr(s->assert_property, visit);
  std::unordered_set<const ModuleItem*> seen;
  bool match_items = TreeHasMatchItems(s->assert_property, sequences, seen);
  if (s->assert_sequence != nullptr) {
    ForEachBodyExpr(s->assert_sequence->seq_linear, visit);
    match_items =
        match_items ||
        BodyHasMatchItems(s->assert_sequence->seq_linear, sequences, seen);
  }
  if (!future ||
      GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(match_items)) {
    return;
  }
  diag.Error(s->range.start,
             "a global clocking future sampled value function may not stand "
             "in an assertion that holds a sequence match item",
             Subclause("16.9.4"));
}

bool SameClockEvent(const Clock& a, const Clock& b) {
  return a.size() == 1 && b.size() == 1 && a[0].edge == b[0].edge &&
         a[0].signal != nullptr && b[0].signal != nullptr &&
         SamePath(a[0].signal, b[0].signal);
}

// §16.13.3: the clock a named sequence ends on: the one flowing out of its
// body, else the last one its chain writes, else its leading clock.
const Clock& EndingClock(const ModuleItem* seq) {
  const SeqLinearBody& body = seq->seq_linear;
  if (!body.clock_out.empty()) return body.clock_out;
  for (size_t i = body.clocks.size(); i > 0; --i) {
    if (!body.clocks[i - 1].empty()) return body.clocks[i - 1];
  }
  return seq->seq_clock;
}

// §16.9.11 and §16.13.5: the ending clock of a sequence triggered is applied
// to is the clock of the context the method stands in, `clock`.
void CheckEndingClocks(const Expr* e, const Clock& clock,
                       const SequenceMap& sequences, DiagEngine& diag) {
  if (clock.size() != 1) return;
  ExprAny(e, [&](const Expr* sub) {
    const ModuleItem* seq = TriggeredSequence(sub, sequences);
    if (seq == nullptr) return false;
    const Clock& ending = EndingClock(seq);
    if (ending.size() == 1 && !SameClockEvent(ending, clock)) {
      diag.Error(sub->range.start,
                 "the ending clock of '" + std::string(seq->name) +
                     "' differs from the clock of the context its triggered "
                     "stands in",
                 Subclause("16.9.11"));
    }
    return false;
  });
}

// The clock in force at each operand of `body`, the one flowing in being
// `clock`, checked against each triggered there.
void CheckBodyEndingClocks(const SeqLinearBody& body, const Clock& clock,
                           const SequenceMap& sequences, DiagEngine& diag) {
  const Clock* in_force = &clock;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    if (i < body.clocks.size() && !body.clocks[i].empty()) {
      in_force = &body.clocks[i];
    }
    CheckEndingClocks(body.operands[i], *in_force, sequences, diag);
  }
}

void CheckTreeEndingClocks(const PropertyExprNode* node, const Clock& clock,
                           const SequenceMap& sequences, DiagEngine& diag) {
  if (node == nullptr) return;
  const Clock& here = node->clock.empty() ? clock : node->clock;
  CheckEndingClocks(node->boolean, here, sequences, diag);
  if (node->sequence != nullptr) {
    const Clock& lead =
        node->sequence->seq_clock.empty() ? here : node->sequence->seq_clock;
    CheckBodyEndingClocks(node->sequence->seq_linear, lead, sequences, diag);
  }
  for (const PropertyExprNode* operand : node->operands) {
    CheckTreeEndingClocks(operand, here, sequences, diag);
  }
}

// The sequences `seq` depends on through triggered, and through instances.
struct TriggeredGraph {
  std::unordered_map<const ModuleItem*, std::vector<const ModuleItem*>>
      triggered;
  std::unordered_map<const ModuleItem*, std::vector<const ModuleItem*>> all;
};

TriggeredGraph BuildTriggeredGraph(const SequenceMap& sequences,
                                   const PropertyRegistry& registry) {
  TriggeredGraph graph;
  for (const auto& [name, seq] : sequences) {
    std::vector<const ModuleItem*>& all = graph.all[seq];
    for (std::string_view ref : registry.DependencyRefs(seq)) {
      auto it = sequences.find(ref);
      if (it != sequences.end()) all.push_back(it->second);
    }
    ForEachBodyExpr(seq->seq_linear, [&](const Expr* e) {
      ExprAny(e, [&](const Expr* sub) {
        const ModuleItem* target = TriggeredSequence(sub, sequences);
        if (target != nullptr) {
          graph.triggered[seq].push_back(target);
          all.push_back(target);
        }
        return false;
      });
    });
  }
  return graph;
}

bool Reaches(const TriggeredGraph& graph, const ModuleItem* from,
             const ModuleItem* to) {
  std::unordered_set<const ModuleItem*> seen;
  std::vector<const ModuleItem*> stack{from};
  while (!stack.empty()) {
    const ModuleItem* cur = stack.back();
    stack.pop_back();
    if (cur == to) return true;
    if (!seen.insert(cur).second) continue;
    auto it = graph.all.find(cur);
    if (it == graph.all.end()) continue;
    stack.insert(stack.end(), it->second.begin(), it->second.end());
  }
  return false;
}

// §16.13.6: no sequence lies on a cycle of dependencies one of whose edges
// is the use of triggered.
void CheckTriggeredCycles(const ModuleDecl* decl, const SequenceMap& sequences,
                          const PropertyRegistry& registry, DiagEngine& diag) {
  TriggeredGraph graph = BuildTriggeredGraph(sequences, registry);
  for (const ModuleItem* seq : decl->items) {
    auto it = graph.triggered.find(seq);
    if (it == graph.triggered.end()) continue;
    for (const ModuleItem* target : it->second) {
      if (!Reaches(graph, target, seq)) continue;
      diag.Error(seq->loc,
                 "the sequence '" + std::string(seq->name) +
                     "' depends on its own end point through triggered",
                 Subclause("16.13.6"));
      break;
    }
  }
}

void CheckAssertion(const Stmt* s, const SequenceMap& sequences,
                    DiagEngine& diag) {
  CheckFutureGclkWithMatchItems(s, sequences, diag);
  CheckTreeEndingClocks(s->assert_property, s->assert_clock, sequences, diag);
}

}  // namespace

void ValidateAssertionContextRules(const ModuleDecl* decl,
                                   const PropertyRegistry& registry,
                                   DiagEngine& diag) {
  const SequenceMap kSequences = NamedDeclsByName(decl, false);
  CheckTriggeredCycles(decl, kSequences, registry, diag);
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      CheckBodyEndingClocks(item->seq_linear, item->seq_clock, kSequences,
                            diag);
    }
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      CheckTreeEndingClocks(item->prop_body_tree, item->prop_clock, kSequences,
                            diag);
    }
  }
  ForEachConcurrentAssertion(
      decl, [&](const Stmt* s) { CheckAssertion(s, kSequences, diag); });
}

}  // namespace delta
