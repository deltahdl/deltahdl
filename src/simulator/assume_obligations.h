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

struct ObligationNode;
enum class ObligationKind : uint8_t;

class AssumeObligations {
 public:
  AssumeObligations(SimContext& ctx, Arena& arena);
  ~AssumeObligations();
  AssumeObligations(const AssumeObligations&) = delete;
  AssumeObligations& operator=(const AssumeObligations&) = delete;

  const ObligationNode* Begin(const Stmt* body, ObligationScope scope,
                              std::vector<Expr*>& reads);

  void NewTimeStep();

  bool Holds(Expr* e);

  void BindLocalsOf(const Expr* e) { terms_.BindLocalsOf(e); }

  Expr* NoFailCondition(const ObligationNode* node, uint32_t ticked);

  const ObligationNode* Step(const ObligationNode* node, uint32_t ticked);

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
  void BuildOperands(const PropertyExprNode* node, int clock,
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
  std::map<std::string, Expr*> instances_;
  std::set<const ModuleItem*> expanding_;
  const ObligationNode* true_ = nullptr;
  const ObligationNode* false_ = nullptr;
  uint32_t ticked_ = ~0u;
  std::map<const Expr*, bool> values_;
  std::map<std::pair<const ObligationNode*, uint32_t>, const ObligationNode*>
      stepped_;
  std::vector<std::pair<const LocalValues*, LocalValues>> frames_;
};

}  // namespace delta
