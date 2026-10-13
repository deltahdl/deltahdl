#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/procedural_concurrent_assertion.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

using Clock = std::vector<EventExpr>;

// The named sequence `e` applies triggered to, null where it applies none.
const ModuleItem* TriggeredSequence(const Expr* e,
                                    const NamedDecls& sequences) {
  return SequenceMethodOf(e) == "triggered"
             ? InstantiatedDecl(e->lhs, sequences)
             : nullptr;
}

// Whether `body`, or a sequence it instantiates, holds a sequence match item;
// `seen` holds the sequences already followed.
bool BodyHasMatchItems(const SeqLinearBody& body, const NamedDecls& sequences,
                       std::unordered_set<const ModuleItem*>& seen);

bool InstantiatesMatchItems(const Expr* e, const NamedDecls& sequences,
                            std::unordered_set<const ModuleItem*>& seen) {
  return AnySubExpr(e, [&](const Expr* sub) {
    const ModuleItem* seq = InstantiatedDecl(sub, sequences);
    return seq != nullptr && seen.insert(seq).second &&
           BodyHasMatchItems(seq->seq_linear, sequences, seen);
  });
}

bool BodyHasMatchItems(const SeqLinearBody& body, const NamedDecls& sequences,
                       std::unordered_set<const ModuleItem*>& seen) {
  bool found = false;
  ForEachBody(body, [&](const SeqLinearBody& b) {
    for (const auto& items : b.match_items) {
      if (!items.empty()) found = true;
    }
  });
  ForEachBodyExpr(body, [&](const Expr* e) {
    if (InstantiatesMatchItems(e, sequences, seen)) found = true;
  });
  return found;
}

bool IsFutureGclk(const Expr* e) {
  GlobalClockingSampledFunction fn{};
  return ClassifyGlobalClockingSampledFunction(e->callee, fn) &&
         IsGlobalClockingFutureFunction(fn);
}

// §16.9.4: a global clocking future sampled value function stands in no
// assertion holding a sequence match item, its own or one reached through
// an instance of a named sequence.
void CheckFutureGclkWithMatchItems(const Stmt* s, const NamedDecls& sequences,
                                   DiagEngine& diag) {
  bool future = false;
  bool match_items = false;
  std::unordered_set<const ModuleItem*> seen;
  ForEachTreeExpr(s->assert_property, [&](const Expr* e) {
    if (AnySubExpr(e, IsFutureGclk)) future = true;
  });
  ForEachTreeNode(s->assert_property, [&](const PropertyExprNode& node) {
    if (InstantiatesMatchItems(node.boolean, sequences, seen)) {
      match_items = true;
    }
    if (node.sequence != nullptr &&
        BodyHasMatchItems(node.sequence->seq_linear, sequences, seen)) {
      match_items = true;
    }
  });
  if (!future ||
      GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(match_items)) {
    return;
  }
  diag.Error(s->range.start,
             "a global clocking future sampled value function may not stand "
             "in an assertion that holds a sequence match item",
             Subclause("16.9.4"));
}

// §16.13.3: the clock a named sequence ends on: the one flowing out of its
// body where the body changes clock, else its leading clock.
const Clock& EndingClock(const ModuleItem* seq) {
  return seq->seq_linear.clock_out.empty() ? seq->seq_clock
                                           : seq->seq_linear.clock_out;
}

// §16.9.11 and §16.13.5: the ending clock of a sequence triggered is applied
// to is the clock of the context the method stands in, `clock`.
void CheckEndingClocks(const Expr* e, const Clock& clock,
                       const NamedDecls& sequences, DiagEngine& diag) {
  ForEachSubExpr(e, [&](const Expr* sub) {
    const ModuleItem* seq = TriggeredSequence(sub, sequences);
    if (seq == nullptr || clock.size() != 1) return;
    const Clock& ending = EndingClock(seq);
    if (ending.size() != 1 || (ending[0].edge == clock[0].edge &&
                               SamePath(ending[0].signal, clock[0].signal))) {
      return;
    }
    diag.Error(sub->range.start,
               "the ending clock of '" + std::string(seq->name) +
                   "' differs from the clock of the context its triggered "
                   "stands in",
               Subclause("16.9.11"));
  });
}

// The clock in force at each operand of `body`, the one flowing in being
// `clock`, checked against each triggered there.
void CheckBodyEndingClocks(const SeqLinearBody& body, const Clock& clock,
                           const NamedDecls& sequences, DiagEngine& diag) {
  const Clock* in_force = &clock;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    if (i < body.clocks.size() && !body.clocks[i].empty()) {
      in_force = &body.clocks[i];
    }
    CheckEndingClocks(body.operands[i], *in_force, sequences, diag);
  }
}

void CheckTreeEndingClocks(const PropertyExprNode* node, const Clock& clock,
                           const NamedDecls& sequences, DiagEngine& diag) {
  if (node == nullptr) return;
  const Clock& here = node->clock.empty() ? clock : node->clock;
  CheckEndingClocks(node->boolean, here, sequences, diag);
  if (node->sequence != nullptr) {
    CheckBodyEndingClocks(node->sequence->seq_linear, here, sequences, diag);
  }
  for (const PropertyExprNode* operand : node->operands) {
    CheckTreeEndingClocks(operand, here, sequences, diag);
  }
}

// The sequences each sequence depends on: through triggered alone, and
// through triggered and its instances.
struct TriggeredGraph {
  std::unordered_map<const ModuleItem*, std::vector<const ModuleItem*>>
      triggered;
  std::unordered_map<const ModuleItem*, std::vector<const ModuleItem*>> all;
};

TriggeredGraph BuildTriggeredGraph(const NamedDecls& sequences,
                                   const PropertyRegistry& registry) {
  TriggeredGraph graph;
  for (const auto& [name, seq] : sequences) {
    std::vector<const ModuleItem*>& triggered = graph.triggered[seq];
    std::vector<const ModuleItem*>& all = graph.all[seq];
    ForEachBodyExpr(seq->seq_linear, [&](const Expr* e) {
      ForEachSubExpr(e, [&](const Expr* sub) {
        const ModuleItem* target = TriggeredSequence(sub, sequences);
        if (target != nullptr) triggered.push_back(target);
      });
    });
    all = triggered;
    for (std::string_view ref : registry.DependencyRefs(seq)) {
      auto it = sequences.find(ref);
      if (it != sequences.end()) all.push_back(it->second);
    }
  }
  return graph;
}

bool Reaches(const TriggeredGraph& graph, const ModuleItem* from,
             const ModuleItem* to,
             std::unordered_set<const ModuleItem*>& seen) {
  if (from == to) return true;
  if (!seen.insert(from).second) return false;
  for (const ModuleItem* next : graph.all.at(from)) {
    if (Reaches(graph, next, to, seen)) return true;
  }
  return false;
}

// §16.13.6: no sequence lies on a cycle of dependencies one of whose edges
// is the use of triggered.
void CheckTriggeredCycles(const ModuleDecl* decl, const NamedDecls& sequences,
                          const PropertyRegistry& registry, DiagEngine& diag) {
  TriggeredGraph graph = BuildTriggeredGraph(sequences, registry);
  for (const ModuleItem* seq : decl->items) {
    auto it = graph.triggered.find(seq);
    if (it == graph.triggered.end()) continue;
    std::unordered_set<const ModuleItem*> seen;
    bool cyclic = false;
    for (const ModuleItem* target : it->second) {
      if (Reaches(graph, target, seq, seen)) cyclic = true;
    }
    if (!cyclic) continue;
    diag.Error(seq->loc,
               "the sequence '" + std::string(seq->name) +
                   "' depends on its own end point through triggered",
               Subclause("16.13.6"));
  }
}

// §16.9.11 with §16.14.6: in a procedure whose clock is inferred, each
// triggered its expressions read, a wait's condition among them, is applied
// to a sequence ending on that clock.
void CheckProcedureEndingClocks(const ModuleItem* item, const RtlirModule* mod,
                                const NamedDecls& sequences, DiagEngine& diag) {
  if (!IsProceduralItemKind(item->kind)) return;
  const Clock kClock = InferredInProcedure(item, mod).clock;
  auto check = [&](const Expr* e) {
    CheckEndingClocks(e, kClock, sequences, diag);
  };
  ForEachStmtReadExpr(item->body, check);
  ForEachProceduralStmt(item, [&](const Stmt* s) {
    if (s->kind == StmtKind::kWait) check(s->condition);
  });
}

}  // namespace

void ValidateAssertionContextRules(const ModuleDecl* decl,
                                   const RtlirModule* mod,
                                   const PropertyRegistry& registry,
                                   DiagEngine& diag) {
  const NamedDecls kSequences = NamedDeclsByName(decl, false);
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
    CheckProcedureEndingClocks(item, mod, kSequences, diag);
  }
  ForEachConcurrentAssertion(decl, [&](const Stmt* s) {
    CheckFutureGclkWithMatchItems(s, kSequences, diag);
    CheckTreeEndingClocks(s->assert_property, s->assert_clock, kSequences,
                          diag);
  });
}

}  // namespace delta
