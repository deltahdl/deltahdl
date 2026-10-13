#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/sequence_flatten.h"

namespace delta {

class Arena;
class SimContext;

// §17.7.2: one state of an attempt of a sequence of Boolean operands under
// cycle delays (§16.7) and repetitions (§16.9.2), read one tick at a time:
// the operand `op` is to be read from `lo` to `hi` ticks after the current
// one, `count` of its repetitions matched; kTail is the run of a
// nonconsecutive repetition past its last match.
struct SeqObligationState {
  enum class Phase : uint8_t { kRun, kTail };
  uint32_t op = 0;
  uint32_t lo = 0;
  uint32_t hi = 0;
  uint32_t count = 0;
  Phase phase = Phase::kRun;
  auto operator<=>(const SeqObligationState&) const = default;
};

// One way an attempt goes at the current tick: the operands it reads there,
// each with the truth it needs, and whether it then matches or goes on from
// the state `next` at the following tick.
struct SeqObligationPath {
  std::vector<std::pair<Expr*, bool>> literals;
  bool match = false;
  SeqObligationState next;
};

// The state an attempt of `seq` begins in, and the ways the attempts in the
// states `states` go at the current tick.
SeqObligationState SeqObligationStart(const LinearSequence& seq);
std::vector<SeqObligationPath> SeqObligationPaths(
    const LinearSequence& seq, const std::vector<SeqObligationState>& states);

// §17.7.2: what one attempt of an assumption still owes from the time step
// it is read at: the property left to hold, written as §16.12's operators
// over booleans and sequences read from that step on. Nodes are shared, so
// that attempts begun at different ticks owing the same are one node.
struct ObligationNode;
enum class ObligationKind : uint8_t;

// Rewrites an expression an assumption reads into the terms of the checker
// whose free variables it constrains: a child checker's formal into its
// actual (§17.7.2).
using ObligationRewrite = std::function<Expr*(Expr*)>;

// §17.7.2: the obligations of the assumptions of one assume set. A solution
// attempt is held to the conditions under which no obligation in flight
// fails in its time step, and once the active free variables take their
// values each obligation steps to what it owes from the next tick on.
class AssumeObligations {
 public:
  AssumeObligations(SimContext& ctx, Arena& arena);
  ~AssumeObligations();
  AssumeObligations(const AssumeObligations&) = delete;
  AssumeObligations& operator=(const AssumeObligations&) = delete;

  // The obligation an attempt of the concurrent assumption `body` begins
  // with, each expression it reads passed through `rewrite` and appended to
  // `reads`; nullptr where its property uses a form the obligations do not
  // model.
  const ObligationNode* Begin(const Stmt* body,
                              const ObligationRewrite& rewrite,
                              std::vector<Expr*>& reads);

  // The condition, over the values the time step reads, under which `node`
  // does not fail in it; nullptr where those values do not decide it.
  Expr* NoFailCondition(const ObligationNode* node);

  // Forgets the values read so far, the active free variables having taken
  // new ones.
  void NewTimeStep();

  // An expression read at its value in the current time step, once.
  bool Holds(Expr* e);

  // What `node` owes from the next tick on, the expressions it reads taken
  // at their values in the current time step.
  const ObligationNode* Step(const ObligationNode* node);

  // Whether `node` owes nothing more, having held or failed.
  bool Settled(const ObligationNode* node) const;

 private:
  const ObligationNode* Intern(ObligationNode node);
  const ObligationNode* Leaf(ObligationKind kind, Expr* e);
  const ObligationNode* Seq(const LinearSequence* seq,
                            std::vector<SeqObligationState> states);
  const ObligationNode* Not(const ObligationNode* a);
  const ObligationNode* Junction(
      ObligationKind kind, const std::vector<const ObligationNode*>& operands);
  const ObligationNode* If(Expr* cond, const ObligationNode* then_node,
                           const ObligationNode* else_node);
  const ObligationNode* Next(uint32_t ticks, const ObligationNode* a);
  const ObligationNode* Over(ObligationKind kind,
                             std::vector<const ObligationNode*> operands,
                             Expr* e = nullptr, uint32_t n = 0);
  const ObligationNode* Expand(const ObligationNode* node);

  const ObligationNode* Build(const PropertyExprNode* node,
                              const ObligationRewrite& rewrite,
                              std::vector<Expr*>& reads);
  const ObligationNode* BuildBool(Expr* e, const ObligationRewrite& rewrite,
                                  std::vector<Expr*>& reads);
  bool BuildOperands(const PropertyExprNode* node,
                     const ObligationRewrite& rewrite,
                     std::vector<Expr*>& reads,
                     std::vector<const ObligationNode*>& out);
  const ObligationNode* BuildSequence(const ModuleItem* item,
                                      const ObligationRewrite& rewrite,
                                      std::vector<Expr*>& reads);
  const ObligationNode* BuildRange(const PropertyExprNode* node,
                                   const ObligationNode* operand,
                                   const ObligationRewrite& rewrite);
  const ObligationNode* BuildCase(
      const PropertyExprNode* node,
      const std::vector<const ObligationNode*>& items,
      const ObligationRewrite& rewrite, std::vector<Expr*>& reads);
  const ObligationNode* BuildConditional(const PropertyExprNode* node,
                                         std::vector<const ObligationNode*> ops,
                                         const ObligationRewrite& rewrite,
                                         std::vector<Expr*>& reads);
  const ObligationNode* BuildImplication(const PropertyExprNode* node,
                                         const ObligationNode* consequent,
                                         const ObligationRewrite& rewrite,
                                         std::vector<Expr*>& reads);
  uint32_t ConstantOf(Expr* e, uint32_t fallback,
                      const ObligationRewrite& rewrite);

  Expr* NotExpr(Expr* a);
  Expr* JoinExpr(Expr* a, Expr* b, bool conjunction);
  Expr* AndExpr(Expr* a, Expr* b);
  Expr* OrExpr(Expr* a, Expr* b);
  Expr* SeqCondition(const ObligationNode* node, bool match);
  Expr* Condition(const ObligationNode* node, bool decided);
  Expr* ConditionOf(const ObligationNode* node, bool decided);
  Expr* ImplicationCondition(const ObligationNode* node, bool decided);
  const std::vector<SeqObligationPath>& PathsOf(const ObligationNode* node);
  bool StepSeq(const ObligationNode* node,
               std::vector<SeqObligationState>& next);
  const ObligationNode* StepOperator(const ObligationNode* node);
  const ObligationNode* StepImplication(const ObligationNode* node);
  const ObligationNode* StepAbort(const ObligationNode* node);

  SimContext& ctx_;
  Arena& arena_;
  std::map<std::string, std::unique_ptr<ObligationNode>> nodes_;
  std::vector<std::unique_ptr<LinearSequence>> sequences_;
  const ObligationNode* true_ = nullptr;
  const ObligationNode* false_ = nullptr;
  // The conditions met under any values and under none, which a condition
  // built from them folds away.
  Expr* always_ = nullptr;
  Expr* never_ = nullptr;
  // Within one step: the values read and the nodes already stepped.
  std::map<const Expr*, bool> values_;
  std::map<const ObligationNode*, const ObligationNode*> stepped_;
};

}  // namespace delta
