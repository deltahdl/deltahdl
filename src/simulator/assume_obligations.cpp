#include "simulator/assume_obligations.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/property_attempts.h"
#include "simulator/sequence_flatten.h"

namespace delta {

// §16.12's operators as an obligation holds them: a boolean, the constants
// among them, a sequence (§16.12.2), not, and and or over operands, if-else
// over `expr`, an implication of a sequence (§16.12.7), overlapping where
// `n` is set, nexttime `n` ticks on (§16.12.10), unbounded always
// (§16.12.11), until and until_with (§16.12.12), unbounded s_eventually
// (§16.12.13), and the aborts over the condition `expr` (§16.12.14).
enum class ObligationKind : uint8_t {
  kBool,
  kSeq,
  kNot,
  kAnd,
  kOr,
  kIf,
  kNext,
  kImplication,
  kAlways,
  kUntil,
  kUntilWith,
  kEventually,
  kAccept,
  kReject,
};

struct ObligationNode {
  ObligationKind kind = ObligationKind::kBool;
  Expr* expr = nullptr;
  uint32_t n = 0;
  std::vector<const ObligationNode*> operands;
  const LinearSequence* seq = nullptr;
  std::vector<SeqObligationState> states;
  // The conditions under which the node does not fail at a tick and under
  // which it holds by it, and a sequence's ways at a tick, each read once.
  mutable std::array<Expr*, 2> conditions = {nullptr, nullptr};
  mutable bool paths_read = false;
  mutable std::vector<SeqObligationPath> paths;
};

namespace {

using Kind = ObligationKind;

std::string KeyOf(const ObligationNode& node) {
  auto id = [](const void* p) {
    return std::to_string(reinterpret_cast<uintptr_t>(p));
  };
  std::string key = std::to_string(static_cast<int>(node.kind)) + ':' +
                    id(node.expr) + ':' + std::to_string(node.n) + ':' +
                    id(node.seq);
  for (const ObligationNode* op : node.operands) key += ',' + id(op);
  for (const SeqObligationState& s : node.states) {
    key += ';' + std::to_string(s.op) + '/' + std::to_string(s.lo) + '/' +
           std::to_string(s.hi) + '/' + std::to_string(s.count) + '/' +
           std::to_string(static_cast<int>(s.phase));
  }
  return key;
}

// §16.12.2: a sequence `flattened` reads whose operands are booleans under
// cycle delays and repetitions alone, none of them repeated from zero, with
// no operand on a clock of its own, no match item, local variable or
// throughout, and no intersect, and, or or first_match.
bool IsPlainSequence(bool flattened, const LinearSequence& seq) {
  auto has_clock = [](const std::vector<EventExpr>& c) { return !c.empty(); };
  auto has_items = [](const std::vector<SeqMatchAssign>& m) {
    return !m.empty();
  };
  auto from_zero = [](const SeqRepetition& r) { return r.min == 0; };
  auto extras =
      static_cast<size_t>(!flattened) + seq.intersects.size() +
      seq.conjuncts.size() + seq.alternatives.size() + seq.nested.size() +
      seq.locals.size() + seq.throughouts.size() +
      static_cast<size_t>(seq.first_match) +
      static_cast<size_t>(
          std::ranges::count_if(seq.operand_clocks, has_clock)) +
      static_cast<size_t>(std::ranges::count_if(seq.match_items, has_items)) +
      static_cast<size_t>(std::ranges::count_if(seq.repetitions, from_zero));
  return extras == 0;
}

}  // namespace

AssumeObligations::AssumeObligations(SimContext& ctx, Arena& arena)
    : ctx_(ctx), arena_(arena) {
  always_ = LiteralOfValue(MakeLogic4VecVal(arena, 1, 1), arena);
  never_ = LiteralOfValue(MakeLogic4VecVal(arena, 1, 0), arena);
  true_ = Leaf(Kind::kBool, always_);
  false_ = Leaf(Kind::kBool, never_);
}

AssumeObligations::~AssumeObligations() = default;

const ObligationNode* AssumeObligations::Intern(ObligationNode node) {
  std::string key = KeyOf(node);
  auto& slot = nodes_[key];
  if (slot == nullptr) {
    slot = std::make_unique<ObligationNode>(std::move(node));
  }
  return slot.get();
}

const ObligationNode* AssumeObligations::Leaf(Kind kind, Expr* e) {
  ObligationNode node;
  node.kind = kind;
  node.expr = e;
  return Intern(std::move(node));
}

const ObligationNode* AssumeObligations::Seq(
    const LinearSequence* seq, std::vector<SeqObligationState> states) {
  std::ranges::sort(states);
  auto [first, last] = std::ranges::unique(states);
  states.erase(first, last);
  if (states.empty()) return false_;
  ObligationNode node;
  node.kind = Kind::kSeq;
  node.seq = seq;
  node.states = std::move(states);
  return Intern(std::move(node));
}

const ObligationNode* AssumeObligations::Not(const ObligationNode* a) {
  if (a == true_) return false_;
  if (a == false_) return true_;
  return Over(Kind::kNot, {a});
}

// §16.12.4 and §16.12.5: an and of operands that hold and an or of operands
// that fail drop them, one an operand decides is that operand's value, and
// an operand of the same operator joins its operands to the others.
const ObligationNode* AssumeObligations::Junction(
    Kind kind, const std::vector<const ObligationNode*>& operands) {
  bool conjunction = kind == Kind::kAnd;
  const ObligationNode* unit = conjunction ? true_ : false_;
  const ObligationNode* zero = conjunction ? false_ : true_;
  std::vector<const ObligationNode*> kept;
  for (const ObligationNode* op : operands) {
    if (op == zero) return zero;
    if (op->kind == kind) {
      kept.insert(kept.end(), op->operands.begin(), op->operands.end());
    } else if (op != unit) {
      kept.push_back(op);
    }
  }
  std::ranges::sort(kept);
  auto [first, last] = std::ranges::unique(kept);
  kept.erase(first, last);
  if (kept.empty()) return unit;
  if (kept.size() == 1) return kept[0];
  return Over(kind, std::move(kept));
}

const ObligationNode* AssumeObligations::If(Expr* cond,
                                            const ObligationNode* then_node,
                                            const ObligationNode* else_node) {
  return Over(Kind::kIf, {then_node, else_node}, cond);
}

const ObligationNode* AssumeObligations::Next(uint32_t ticks,
                                              const ObligationNode* a) {
  if (ticks == 0) return a;
  return Over(Kind::kNext, {a}, nullptr, ticks);
}

const ObligationNode* AssumeObligations::Over(
    Kind kind, std::vector<const ObligationNode*> operands, Expr* e,
    uint32_t n) {
  ObligationNode node;
  node.kind = kind;
  node.operands = std::move(operands);
  node.expr = e;
  node.n = n;
  return Intern(std::move(node));
}

// §16.12.11 to §16.12.13: the operators that carry an obligation to later
// ticks, read as what they owe at this tick and from the next on: `always
// p` as `p and nexttime always p`, `p until q` as `q or (p and nexttime (p
// until q))`, until_with as `(p and q) or (p and nexttime (p until_with
// q))`, and `s_eventually p` as `p or nexttime s_eventually p`.
const ObligationNode* AssumeObligations::Expand(const ObligationNode* node) {
  const ObligationNode* later = Next(1, node);
  const ObligationNode* p = node->operands[0];
  switch (node->kind) {
    case Kind::kAlways:
      return Junction(Kind::kAnd, {p, later});
    case Kind::kUntil:
      return Junction(Kind::kOr,
                      {node->operands[1], Junction(Kind::kAnd, {p, later})});
    case Kind::kUntilWith:
      return Junction(Kind::kOr, {Junction(Kind::kAnd, {p, node->operands[1]}),
                                  Junction(Kind::kAnd, {p, later})});
    default:
      return Junction(Kind::kOr, {p, later});
  }
}

// An elaboration-time constant (§16.12.10 to §16.12.13), `fallback` where
// none was written.
uint32_t AssumeObligations::ConstantOf(Expr* e, uint32_t fallback,
                                       const ObligationRewrite& rewrite) {
  if (e == nullptr) return fallback;
  return static_cast<uint32_t>(EvalExpr(rewrite(e), ctx_, arena_).ToUint64());
}

const ObligationNode* AssumeObligations::Begin(const Stmt* body,
                                               const ObligationRewrite& rewrite,
                                               std::vector<Expr*>& reads) {
  if (body->assert_property != nullptr) {
    return Build(body->assert_property, rewrite, reads);
  }
  const ObligationNode* node =
      body->assert_sequence != nullptr
          ? BuildSequence(body->assert_sequence, rewrite, reads)
          : BuildBool(body->assert_expr, rewrite, reads);
  if (node == nullptr || !body->assert_negated) return node;
  return Not(node);
}

// A boolean the property reads, or nullptr where the operand instantiates a
// named property (§16.12.17).
const ObligationNode* AssumeObligations::BuildBool(
    Expr* e, const ObligationRewrite& rewrite, std::vector<Expr*>& reads) {
  if (InstantiatedProperty(e, ctx_) != nullptr) return nullptr;
  Expr* read = rewrite(e);
  reads.push_back(read);
  return Leaf(Kind::kBool, read);
}

const ObligationNode* AssumeObligations::BuildSequence(
    const ModuleItem* item, const ObligationRewrite& rewrite,
    std::vector<Expr*>& reads) {
  auto seq = std::make_unique<LinearSequence>();
  bool flattened = FlattenLinearSequence(item, ctx_, arena_, *seq);
  if (!IsPlainSequence(flattened, *seq)) return nullptr;
  for (Expr*& operand : seq->operands) {
    operand = rewrite(operand);
    reads.push_back(operand);
  }
  const LinearSequence* held = seq.get();
  sequences_.push_back(std::move(seq));
  return Seq(held, {SeqObligationStart(*held)});
}

// Each operand of `node` built in turn into `out`; false where one is of a
// form the obligations do not model.
bool AssumeObligations::BuildOperands(const PropertyExprNode* node,
                                      const ObligationRewrite& rewrite,
                                      std::vector<Expr*>& reads,
                                      std::vector<const ObligationNode*>& out) {
  for (const PropertyExprNode* operand : node->operands) {
    const ObligationNode* built = Build(operand, rewrite, reads);
    if (built == nullptr) return false;
    out.push_back(built);
  }
  return true;
}

// §16.12.10 to §16.12.13: nexttime, always and eventually over their
// ranges, a bounded range being the and, or for eventually the or, of the
// operand at each tick it covers.
const ObligationNode* AssumeObligations::BuildRange(
    const PropertyExprNode* node, const ObligationNode* operand,
    const ObligationRewrite& rewrite) {
  if (node->kind == PropertyExprNode::Kind::kNexttime) {
    return Next(ConstantOf(node->boolean, 1, rewrite), operand);
  }
  bool always = node->kind == PropertyExprNode::Kind::kAlways;
  uint32_t lo = ConstantOf(node->range_min, 0, rewrite);
  if (node->range_unbounded) {
    return Next(lo,
                Over(always ? Kind::kAlways : Kind::kEventually, {operand}));
  }
  uint32_t hi = ConstantOf(node->range_max, 0, rewrite);
  std::vector<const ObligationNode*> ticks;
  ticks.reserve(hi - lo + 1);
  for (uint32_t t = lo; t <= hi; ++t) ticks.push_back(Next(t, operand));
  return Junction(always ? Kind::kAnd : Kind::kOr, ticks);
}

// §16.12.16: the first item whose expression the case expression matches
// is selected, the default where none does, and the case holds where no
// item is selected.
const ObligationNode* AssumeObligations::BuildCase(
    const PropertyExprNode* node,
    const std::vector<const ObligationNode*>& items,
    const ObligationRewrite& rewrite, std::vector<Expr*>& reads) {
  Expr* selector = rewrite(node->boolean);
  reads.push_back(selector);
  const ObligationNode* result = true_;
  for (size_t i = 0; i < node->case_values.size(); ++i) {
    if (node->case_values[i].empty()) result = items[i];
  }
  for (size_t i = node->case_values.size(); i-- > 0;) {
    Expr* matches = never_;
    for (Expr* value : node->case_values[i]) {
      auto* eq = arena_.Create<Expr>();
      eq->kind = ExprKind::kBinary;
      eq->op = TokenKind::kEqEqEq;
      eq->lhs = selector;
      eq->rhs = rewrite(value);
      reads.push_back(eq->rhs);
      matches = OrExpr(matches, eq);
    }
    if (matches != never_) result = If(matches, items[i], result);
  }
  return result;
}

const ObligationNode* AssumeObligations::Build(const PropertyExprNode* node,
                                               const ObligationRewrite& rewrite,
                                               std::vector<Expr*>& reads) {
  using P = PropertyExprNode::Kind;
  if (!node->clock.empty()) return nullptr;
  if (node->kind == P::kBoolean) {
    return BuildBool(node->boolean, rewrite, reads);
  }
  if (node->kind == P::kSequence) {
    return BuildSequence(node->sequence, rewrite, reads);
  }
  std::vector<const ObligationNode*> ops;
  if (!BuildOperands(node, rewrite, reads, ops)) return nullptr;
  switch (node->kind) {
    case P::kNot:
      return Not(ops[0]);
    case P::kOr:
      return Junction(Kind::kOr, ops);
    case P::kAnd:
      return Junction(Kind::kAnd, ops);
    case P::kImplies:
      return Junction(Kind::kOr, {Not(ops[0]), ops[1]});
    case P::kIff:
      return Junction(Kind::kOr,
                      {Junction(Kind::kAnd, {ops[0], ops[1]}),
                       Junction(Kind::kAnd, {Not(ops[0]), Not(ops[1])})});
    case P::kUntil:
      return Over(node->range_unbounded ? Kind::kUntilWith : Kind::kUntil,
                  std::move(ops));
    case P::kNexttime:
    case P::kAlways:
    case P::kEventually:
      return BuildRange(node, ops[0], rewrite);
    case P::kImplication:
      return BuildImplication(node, ops[0], rewrite, reads);
    case P::kCase:
      return BuildCase(node, ops, rewrite, reads);
    default:
      return BuildConditional(node, std::move(ops), rewrite, reads);
  }
}

// §16.12.6 and §16.12.14: an if-else, its else holding where none was
// written, and an abort, over the condition they read.
const ObligationNode* AssumeObligations::BuildConditional(
    const PropertyExprNode* node, std::vector<const ObligationNode*> ops,
    const ObligationRewrite& rewrite, std::vector<Expr*>& reads) {
  Expr* cond = rewrite(node->boolean);
  reads.push_back(cond);
  if (node->kind == PropertyExprNode::Kind::kIfElse) {
    return If(cond, ops[0], ops.size() > 1 ? ops[1] : true_);
  }
  return Over(node->accept ? Kind::kAccept : Kind::kReject, std::move(ops),
              cond);
}

// §16.12.7: an implication whose antecedent is a sequence the obligations
// model, overlapping where it is `|->`.
const ObligationNode* AssumeObligations::BuildImplication(
    const PropertyExprNode* node, const ObligationNode* consequent,
    const ObligationRewrite& rewrite, std::vector<Expr*>& reads) {
  const ObligationNode* antecedent =
      BuildSequence(node->sequence, rewrite, reads);
  if (antecedent == nullptr) return nullptr;
  return Over(Kind::kImplication, {antecedent, consequent}, nullptr,
              node->strong ? 0 : 1);
}

Expr* AssumeObligations::NotExpr(Expr* a) {
  if (a == always_) return never_;
  if (a == never_) return always_;
  auto* e = arena_.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = TokenKind::kBang;
  e->lhs = a;
  return e;
}

// `a && b`, or `a || b` where `conjunction` is unset, a constant operand
// folded away.
Expr* AssumeObligations::JoinExpr(Expr* a, Expr* b, bool conjunction) {
  Expr* unit = conjunction ? always_ : never_;
  Expr* zero = conjunction ? never_ : always_;
  if (a == zero || b == zero) return zero;
  if (a == unit) return b;
  if (b == unit) return a;
  auto* e = arena_.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = conjunction ? TokenKind::kAmpAmp : TokenKind::kPipePipe;
  e->lhs = a;
  e->rhs = b;
  return e;
}

Expr* AssumeObligations::AndExpr(Expr* a, Expr* b) {
  return JoinExpr(a, b, true);
}

Expr* AssumeObligations::OrExpr(Expr* a, Expr* b) {
  return JoinExpr(a, b, false);
}

const std::vector<SeqObligationPath>& AssumeObligations::PathsOf(
    const ObligationNode* node) {
  if (!node->paths_read) {
    node->paths = SeqObligationPaths(*node->seq, node->states);
    node->paths_read = true;
  }
  return node->paths;
}

// The condition under which an attempt of the sequence `node` matches at
// this tick, or, `match` unset, goes on past it.
Expr* AssumeObligations::SeqCondition(const ObligationNode* node, bool match) {
  Expr* any = never_;
  for (const SeqObligationPath& path : PathsOf(node)) {
    if (path.match != match) continue;
    Expr* all = always_;
    for (const auto& [operand, value] : path.literals) {
      all = AndExpr(all, value ? operand : NotExpr(operand));
    }
    any = OrExpr(any, all);
  }
  return any;
}

// The condition under which `node` does not fail at this tick, or, where
// `decided` is set, under which it holds by this tick and owes nothing
// more.
Expr* AssumeObligations::Condition(const ObligationNode* node, bool decided) {
  Expr*& memo = node->conditions[decided ? 1 : 0];
  if (memo == nullptr) memo = ConditionOf(node, decided);
  return memo;
}

Expr* AssumeObligations::ConditionOf(const ObligationNode* node, bool decided) {
  const auto& ops = node->operands;
  bool conjunction = node->kind == Kind::kAnd;
  Expr* all = conjunction ? always_ : never_;
  switch (node->kind) {
    case Kind::kBool:
      return node->expr;
    case Kind::kSeq:
      return OrExpr(SeqCondition(node, true),
                    decided ? never_ : SeqCondition(node, false));
    case Kind::kNot:
      return NotExpr(Condition(ops[0], !decided));
    case Kind::kAnd:
    case Kind::kOr:
      for (const ObligationNode* op : ops) {
        all = JoinExpr(all, Condition(op, decided), conjunction);
      }
      return all;
    case Kind::kIf:
      return OrExpr(AndExpr(node->expr, Condition(ops[0], decided)),
                    AndExpr(NotExpr(node->expr), Condition(ops[1], decided)));
    case Kind::kNext:
      return decided ? never_ : always_;
    case Kind::kImplication:
      return ImplicationCondition(node, decided);
    case Kind::kAccept:
      return OrExpr(node->expr, Condition(ops[0], decided));
    case Kind::kReject:
      return AndExpr(NotExpr(node->expr), Condition(ops[0], decided));
    default:
      return Condition(Expand(node), decided);
  }
}

// §16.12.7: an implication fails at this tick where its antecedent matches
// there and the consequent begun at the match fails at once, which a
// nonoverlapped one, begun at the next tick, never does; it holds once its
// antecedent can match no more and every consequent begun has held.
Expr* AssumeObligations::ImplicationCondition(const ObligationNode* node,
                                              bool decided) {
  const ObligationNode* antecedent = node->operands[0];
  const ObligationNode* consequent = node->operands[1];
  Expr* begun =
      Condition(node->n != 0 ? consequent : Next(1, consequent), decided);
  Expr* now = OrExpr(NotExpr(SeqCondition(antecedent, true)), begun);
  if (!decided) return now;
  return AndExpr(NotExpr(SeqCondition(antecedent, false)), now);
}

Expr* AssumeObligations::NoFailCondition(const ObligationNode* node) {
  Expr* cond = Condition(node, false);
  return cond == always_ || cond == never_ ? nullptr : cond;
}

void AssumeObligations::NewTimeStep() {
  values_.clear();
  stepped_.clear();
}

bool AssumeObligations::Holds(Expr* e) {
  auto found = values_.find(e);
  if (found != values_.end()) return found->second;
  bool value = EvalExpr(e, ctx_, arena_).IsTruthy();
  values_[e] = value;
  return value;
}

bool AssumeObligations::Settled(const ObligationNode* node) const {
  return node == true_ || node == false_;
}

// The ways of the sequence `node` taken at this tick, `next` collecting the
// states they go on in; true where one matches.
bool AssumeObligations::StepSeq(const ObligationNode* node,
                                std::vector<SeqObligationState>& next) {
  bool matched = false;
  for (const SeqObligationPath& path : PathsOf(node)) {
    bool taken = std::ranges::all_of(path.literals, [&](const auto& lit) {
      return Holds(lit.first) == lit.second;
    });
    if (!taken) continue;
    matched = matched || path.match;
    if (!path.match) next.push_back(path.next);
  }
  return matched;
}

const ObligationNode* AssumeObligations::Step(const ObligationNode* node) {
  auto found = stepped_.find(node);
  if (found != stepped_.end()) return found->second;
  const ObligationNode* result = StepOperator(node);
  stepped_[node] = result;
  return result;
}

const ObligationNode* AssumeObligations::StepOperator(
    const ObligationNode* node) {
  const auto& ops = node->operands;
  std::vector<SeqObligationState> next;
  std::vector<const ObligationNode*> stepped;
  switch (node->kind) {
    case Kind::kBool:
      return Holds(node->expr) ? true_ : false_;
    case Kind::kSeq:
      return StepSeq(node, next) ? true_ : Seq(node->seq, std::move(next));
    case Kind::kNot:
      return Not(Step(ops[0]));
    case Kind::kAnd:
    case Kind::kOr:
      stepped.reserve(ops.size());
      for (const ObligationNode* op : ops) stepped.push_back(Step(op));
      return Junction(node->kind, stepped);
    case Kind::kIf:
      return Step(ops[Holds(node->expr) ? 0 : 1]);
    case Kind::kNext:
      return Next(node->n - 1, ops[0]);
    case Kind::kImplication:
      return StepImplication(node);
    case Kind::kAccept:
    case Kind::kReject:
      return StepAbort(node);
    default:
      return Step(Expand(node));
  }
}

// §16.12.7: each match of the antecedent at this tick begins an attempt of
// the consequent, at this tick for `|->` and the next for `|=>`, and the
// antecedent goes on while it can match again.
const ObligationNode* AssumeObligations::StepImplication(
    const ObligationNode* node) {
  const ObligationNode* antecedent = node->operands[0];
  const ObligationNode* consequent = node->operands[1];
  std::vector<SeqObligationState> next;
  const ObligationNode* begun = true_;
  if (StepSeq(antecedent, next)) {
    begun = node->n != 0 ? Step(consequent) : consequent;
  }
  const ObligationNode* rest = true_;
  if (!next.empty()) {
    rest = Over(Kind::kImplication,
                {Seq(antecedent->seq, std::move(next)), consequent}, nullptr,
                node->n);
  }
  return Junction(Kind::kAnd, {begun, rest});
}

// §16.12.14: an abort whose condition holds at this tick decides the
// property, accept_on as holding and reject_on as failing; otherwise its
// operand goes on under it.
const ObligationNode* AssumeObligations::StepAbort(const ObligationNode* node) {
  if (Holds(node->expr)) return node->kind == Kind::kAccept ? true_ : false_;
  const ObligationNode* operand = Step(node->operands[0]);
  if (Settled(operand)) return operand;
  return Over(node->kind, {operand}, node->expr);
}

}  // namespace delta
