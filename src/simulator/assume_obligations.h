#pragma once

#include <cstdint>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/assume_sequence_terms.h"

namespace delta {

class Arena;
class SimContext;

// §17.7.2: what one attempt of an assumption still owes from the time step
// it is read at: the property left to hold, written as §16.12's operators
// over booleans and sequences read from that step on, each on the clock it
// is evaluated on (§16.13). Nodes are shared, so that attempts begun at
// different ticks owing the same are one node.
struct ObligationNode;
enum class ObligationKind : uint8_t;

// §17.7.2: the obligations of the assumptions of one assume set. A solution
// attempt is held to the conditions under which no obligation in flight
// fails in its time step, and once the active free variables take their
// values each obligation steps to what it owes from the next tick on. The
// clocks that ticked at the time step, a bit each by their number, say
// which of the obligations' operands are read there.
class AssumeObligations {
 public:
  AssumeObligations(SimContext& ctx, Arena& arena);
  ~AssumeObligations();
  AssumeObligations(const AssumeObligations&) = delete;
  AssumeObligations& operator=(const AssumeObligations&) = delete;

  // The obligation an attempt of the concurrent assumption `body` begins
  // with, read in `scope`, each expression it reads appended to `reads`;
  // nullptr where its property uses a form the obligations do not model.
  const ObligationNode* Begin(const Stmt* body, ObligationScope scope,
                              std::vector<Expr*>& reads);

  // Forgets the values read so far, the active free variables having taken
  // new ones.
  void NewTimeStep();

  // An expression read at its value in the current time step, once.
  bool Holds(Expr* e);

  // The condition, over the values the time step reads, under which `node`
  // does not fail in it, the clocks `ticked` having ticked; nullptr where
  // it holds under any values.
  Expr* NoFailCondition(const ObligationNode* node, uint32_t ticked);

  // What `node` owes from the next tick on, the expressions it reads taken
  // at their values in the current time step.
  const ObligationNode* Step(const ObligationNode* node, uint32_t ticked);

  // Whether `node` owes nothing more, having held or failed.
  bool Settled(const ObligationNode* node) const;

 private:
  const ObligationNode* Intern(ObligationNode node);
  const ObligationNode* Leaf(Expr* e, int clock);
  const ObligationNode* Seq(std::vector<const SeqTerm*> terms, bool fresh);
  const ObligationNode* Not(const ObligationNode* a);
  const ObligationNode* Junction(
      ObligationKind kind, const std::vector<const ObligationNode*>& operands);
  const ObligationNode* WithLocals(const LocalValues* locals,
                                   const ObligationNode* inner);
  const ObligationNode* Next(uint32_t ticks, const ObligationNode* a,
                             int clock);
  const ObligationNode* Over(ObligationKind kind,
                             std::vector<const ObligationNode*> operands,
                             Expr* e = nullptr, uint32_t n = 0, int clock = 0);
  const ObligationNode* Expand(const ObligationNode* node);
  const ObligationNode* Expansion(const ObligationNode* node,
                                  std::vector<Expr*>& reads);

  const ObligationNode* Build(const PropertyExprNode* node, int clock,
                              const ObligationScope& scope,
                              std::vector<Expr*>& reads);
  const ObligationNode* BuildBool(Expr* e, int clock,
                                  const ObligationScope& scope,
                                  std::vector<Expr*>& reads);
  const ObligationNode* BuildInstance(Expr* e, const ModuleItem* decl,
                                      int clock, const ObligationScope& scope,
                                      std::vector<Expr*>& reads);
  bool BuildOperands(const PropertyExprNode* node, int clock,
                     const ObligationScope& scope, std::vector<Expr*>& reads,
                     std::vector<const ObligationNode*>& out);
  const ObligationNode* BuildSequence(const ModuleItem* item, int clock,
                                      const ObligationScope& scope,
                                      std::vector<Expr*>& reads,
                                      int& clock_out);
  const ObligationNode* BuildRange(const PropertyExprNode* node,
                                   const ObligationNode* operand, int clock,
                                   const ObligationScope& scope);
  const ObligationNode* BuildCase(
      const PropertyExprNode* node,
      const std::vector<const ObligationNode*>& items, int clock,
      const ObligationScope& scope, std::vector<Expr*>& reads);
  const ObligationNode* BuildConditional(const PropertyExprNode* node,
                                         std::vector<const ObligationNode*> ops,
                                         int clock,
                                         const ObligationScope& scope,
                                         std::vector<Expr*>& reads);
  const ObligationNode* BuildImplication(const PropertyExprNode* node,
                                         int clock,
                                         const ObligationScope& scope,
                                         std::vector<Expr*>& reads);
  uint32_t ConstantOf(Expr* e, uint32_t fallback, const ObligationScope& scope);

  bool Ticked(int clock) const;
  Expr* SeqCondition(const ObligationNode* node, bool match);
  Expr* Condition(const ObligationNode* node, bool decided);
  Expr* ConditionOf(const ObligationNode* node, bool decided);
  Expr* ImplicationCondition(const ObligationNode* node, bool decided);
  bool StepSeq(const ObligationNode* node, std::vector<const SeqTerm*>& next);
  const ObligationNode* StepNode(const ObligationNode* node);
  const ObligationNode* StepOperator(const ObligationNode* node);
  const ObligationNode* StepImplication(const ObligationNode* node);
  const ObligationNode* StepAbort(const ObligationNode* node);
  const ObligationNode* StepLocals(const ObligationNode* node);
  Expr* UnderLocals(Expr* cond, const LocalValues* locals);

  SimContext& ctx_;
  Arena& arena_;
  ConditionBuilder conditions_;
  SeqTerms terms_;
  std::map<std::string, std::unique_ptr<ObligationNode>> nodes_;
  std::vector<std::unique_ptr<ObligationScope>> scopes_;
  // §16.12.17: the first instance met of each declaration and actuals, which
  // the expansions of a recursive property share, and the declarations
  // being expanded.
  std::map<std::string, Expr*> instances_;
  std::set<const ModuleItem*> expanding_;
  const ObligationNode* true_ = nullptr;
  const ObligationNode* false_ = nullptr;
  // Within one time step: the clocks that ticked, the values read and the
  // nodes already stepped.
  uint32_t ticked_ = ~0u;
  std::map<const Expr*, bool> values_;
  std::map<std::pair<const ObligationNode*, uint32_t>, const ObligationNode*>
      stepped_;
  // §16.10: the locals of the properties being stepped, innermost last:
  // the values their expressions read, and the values their match items
  // leave.
  std::vector<std::pair<const LocalValues*, LocalValues>> frames_;
};

}  // namespace delta
