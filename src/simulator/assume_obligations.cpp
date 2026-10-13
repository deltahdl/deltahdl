#include "simulator/assume_obligations.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/assume_sequence_terms.h"
#include "simulator/evaluation.h"
#include "simulator/property_attempts.h"
#include "simulator/sequence_flatten.h"

namespace delta {

// §16.12's operators as an obligation holds them: a boolean, the constants
// among them; the sequences an attempt may be in (§16.12.2); not, and and
// or over operands; if-else over `expr`; an implication of a sequence
// (§16.12.7), overlapping where `n` is set; nexttime `n` ticks on
// (§16.12.10); unbounded always (§16.12.11); until and until_with
// (§16.12.12); unbounded s_eventually (§16.12.13); the aborts over the
// condition `expr` (§16.12.14); and an instance of the named property
// `decl` (§16.12.17).
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
  kInstance,
};

struct ObligationNode {
  ObligationKind kind = ObligationKind::kBool;
  Expr* expr = nullptr;
  uint32_t n = 0;
  // §16.13: the number of the clock the node is evaluated on; and, for the
  // sequences, whether the tick read is the one they were begun at.
  int clock = 0;
  bool fresh = false;
  std::vector<const ObligationNode*> operands;
  std::vector<const SeqTerm*> terms;
  // §16.12.17: an instance's declaration, the terms of the assumption it
  // stands in, and the terms of the first body it was met in, which its
  // actuals are read in.
  const ModuleItem* decl = nullptr;
  const ObligationScope* scope = nullptr;
  const ObligationScope* outer = nullptr;
  // The conditions under which the node does not fail at a tick and under
  // which it holds by it, by the clocks that ticked, each read once; and an
  // instance's expansion.
  mutable std::map<uint64_t, Expr*> conditions;
  mutable const ObligationNode* expansion = nullptr;
};

namespace {

using Kind = ObligationKind;

// The clock of the constants, which hold or fail at every time step.
constexpr int kEveryClock = 32;

std::string Id(const void* p) {
  return std::to_string(reinterpret_cast<uintptr_t>(p));
}

std::string KeyOf(const ObligationNode& node) {
  std::string key = std::to_string(static_cast<int>(node.kind)) + ':' +
                    Id(node.expr) + ':' + std::to_string(node.n) + ':' +
                    std::to_string(node.clock) + ':' +
                    std::to_string(static_cast<int>(node.fresh)) + ':' +
                    Id(node.decl) + ':' + Id(node.scope);
  for (const ObligationNode* op : node.operands) key += ',' + Id(op);
  for (const SeqTerm* term : node.terms) key += ';' + Id(term);
  return key;
}

}  // namespace

AssumeObligations::AssumeObligations(SimContext& ctx, Arena& arena)
    : ctx_(ctx),
      arena_(arena),
      conditions_(arena),
      terms_(ctx, arena, conditions_) {
  true_ = Leaf(conditions_.Always(), kEveryClock);
  false_ = Leaf(conditions_.Never(), kEveryClock);
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

const ObligationNode* AssumeObligations::Leaf(Expr* e, int clock) {
  return Over(Kind::kBool, {}, e, 0, clock);
}

const ObligationNode* AssumeObligations::Seq(std::vector<const SeqTerm*> terms,
                                             bool fresh) {
  std::ranges::sort(terms);
  auto [first, last] = std::ranges::unique(terms);
  terms.erase(first, last);
  if (terms.empty()) return false_;
  ObligationNode node;
  node.kind = Kind::kSeq;
  node.terms = std::move(terms);
  node.fresh = fresh;
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

const ObligationNode* AssumeObligations::Next(uint32_t ticks,
                                              const ObligationNode* a,
                                              int clock) {
  if (ticks == 0) return a;
  return Over(Kind::kNext, {a}, nullptr, ticks, clock);
}

const ObligationNode* AssumeObligations::Over(
    Kind kind, std::vector<const ObligationNode*> operands, Expr* e, uint32_t n,
    int clock) {
  ObligationNode node;
  node.kind = kind;
  node.operands = std::move(operands);
  node.expr = e;
  node.n = n;
  node.clock = clock;
  return Intern(std::move(node));
}

// §16.12.11 to §16.12.13: the operators that carry an obligation to later
// ticks of their clock, read as what they owe at this tick and from the
// next on: `always p` as `p and nexttime always p`, `p until q` as `q or (p
// and nexttime (p until q))`, until_with as `(p and q) or (p and nexttime
// (p until_with q))`, and `s_eventually p` as `p or nexttime s_eventually
// p`.
const ObligationNode* AssumeObligations::Expand(const ObligationNode* node) {
  const ObligationNode* later = Next(1, node, node->clock);
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

// §16.12.17: an instance stands for the declaration's body read with the
// actuals in the formals' places, its sequences' operands among them, on
// the clock the declaration names or the one flowing to the instance; an
// instance met while its own declaration is being expanded is expanded
// when it is read, so that a recursive property is expanded a tick at a
// time and its expansions, sharing the instance, are one node. Where the
// body is of a form the obligations do not model, it puts no condition on
// the time step.
const ObligationNode* AssumeObligations::Expansion(const ObligationNode* node,
                                                   std::vector<Expr*>& reads) {
  if (node->expansion != nullptr) return node->expansion;
  const ModuleItem* decl = node->decl;
  const ObligationScope* outer = node->outer;
  ActualsByFormal actuals = BindInstanceActuals(decl, node->expr, arena_);
  scopes_.push_back(std::make_unique<ObligationScope>(ObligationScope{
      [rewrite = outer->rewrite, actuals, &arena = arena_](Expr* e) {
        return rewrite(SubstituteFormals(e, actuals, arena));
      },
      outer->clocks, node->scope}));
  const ObligationScope& inner = *scopes_.back();
  int clock =
      NumberClock(decl->prop_clock, node->clock, inner.rewrite, inner.clocks);
  expanding_.insert(decl);
  const ObligationNode* built =
      Build(decl->prop_body_tree, clock, inner, reads);
  expanding_.erase(decl);
  node->expansion = built != nullptr ? built : true_;
  return built;
}

// An elaboration-time constant (§16.12.10 to §16.12.13), `fallback` where
// none was written.
uint32_t AssumeObligations::ConstantOf(Expr* e, uint32_t fallback,
                                       const ObligationScope& scope) {
  if (e == nullptr) return fallback;
  return static_cast<uint32_t>(
      EvalExpr(scope.rewrite(e), ctx_, arena_).ToUint64());
}

const ObligationNode* AssumeObligations::Begin(const Stmt* body,
                                               ObligationScope scope,
                                               std::vector<Expr*>& reads) {
  scopes_.push_back(std::make_unique<ObligationScope>(std::move(scope)));
  const ObligationScope& held = *scopes_.back();
  if (body->assert_property != nullptr) {
    return Build(body->assert_property, 0, held, reads);
  }
  int clock_out = 0;
  const ObligationNode* node =
      body->assert_sequence != nullptr
          ? BuildSequence(body->assert_sequence, 0, held, reads, clock_out)
          : BuildBool(body->assert_expr, 0, held, reads);
  if (node == nullptr || !body->assert_negated) return node;
  return Not(node);
}

// A boolean the property reads, or the named property the operand
// instantiates (§16.12.17).
const ObligationNode* AssumeObligations::BuildBool(Expr* e, int clock,
                                                   const ObligationScope& scope,
                                                   std::vector<Expr*>& reads) {
  if (const ModuleItem* decl = InstantiatedProperty(e, ctx_)) {
    return BuildInstance(e, decl, clock, scope, reads);
  }
  Expr* read = scope.rewrite(e);
  reads.push_back(read);
  return Leaf(read, clock);
}

// §16.12.17: an instance of `decl`, expanded where it is met unless its
// declaration is being expanded, and nullptr where the declaration holds
// local variables or a body of a form the obligations do not model.
const ObligationNode* AssumeObligations::BuildInstance(
    Expr* e, const ModuleItem* decl, int clock, const ObligationScope& scope,
    std::vector<Expr*>& reads) {
  if (!decl->prop_locals.empty()) return nullptr;
  const ObligationScope* base = scope.base != nullptr ? scope.base : &scope;
  std::string key = Id(decl) + ':' + Id(base);
  for (const Expr* arg : e->args) key += ',' + Id(arg);
  for (std::string_view name : e->arg_names) key += ';' + std::string(name);
  Expr*& first = instances_[key];
  if (first == nullptr) first = e;
  ObligationNode node;
  node.kind = Kind::kInstance;
  node.expr = first;
  node.clock = clock;
  node.decl = decl;
  node.scope = base;
  node.outer = &scope;
  const ObligationNode* instance = Intern(std::move(node));
  if (expanding_.count(decl) != 0) return instance;
  if (Expansion(instance, reads) == nullptr) return nullptr;
  return instance;
}

const ObligationNode* AssumeObligations::BuildSequence(
    const ModuleItem* item, int clock, const ObligationScope& scope,
    std::vector<Expr*>& reads, int& clock_out) {
  const SeqTerm* term = terms_.Begin(item, clock, scope, reads, clock_out);
  if (term == nullptr) return nullptr;
  return Seq({term}, true);
}

// Each operand of `node` built in turn into `out`; false where one is of a
// form the obligations do not model.
bool AssumeObligations::BuildOperands(const PropertyExprNode* node, int clock,
                                      const ObligationScope& scope,
                                      std::vector<Expr*>& reads,
                                      std::vector<const ObligationNode*>& out) {
  for (const PropertyExprNode* operand : node->operands) {
    const ObligationNode* built = Build(operand, clock, scope, reads);
    if (built == nullptr) return false;
    out.push_back(built);
  }
  return true;
}

// §16.12.10 to §16.12.13: nexttime, always and eventually over their
// ranges, a bounded range being the and, or for eventually the or, of the
// operand at each tick it covers.
const ObligationNode* AssumeObligations::BuildRange(
    const PropertyExprNode* node, const ObligationNode* operand, int clock,
    const ObligationScope& scope) {
  if (node->kind == PropertyExprNode::Kind::kNexttime) {
    return Next(ConstantOf(node->boolean, 1, scope), operand, clock);
  }
  bool always = node->kind == PropertyExprNode::Kind::kAlways;
  uint32_t lo = ConstantOf(node->range_min, 0, scope);
  if (node->range_unbounded) {
    return Next(lo,
                Over(always ? Kind::kAlways : Kind::kEventually, {operand},
                     nullptr, 0, clock),
                clock);
  }
  uint32_t hi = ConstantOf(node->range_max, 0, scope);
  std::vector<const ObligationNode*> ticks;
  ticks.reserve(hi - lo + 1);
  for (uint32_t t = lo; t <= hi; ++t) ticks.push_back(Next(t, operand, clock));
  return Junction(always ? Kind::kAnd : Kind::kOr, ticks);
}

// §16.12.16: the first item whose expression the case expression matches
// is selected, the default where none does, and the case holds where no
// item is selected.
const ObligationNode* AssumeObligations::BuildCase(
    const PropertyExprNode* node,
    const std::vector<const ObligationNode*>& items, int clock,
    const ObligationScope& scope, std::vector<Expr*>& reads) {
  Expr* selector = scope.rewrite(node->boolean);
  reads.push_back(selector);
  const ObligationNode* result = true_;
  for (size_t i = 0; i < node->case_values.size(); ++i) {
    if (node->case_values[i].empty()) result = items[i];
  }
  for (size_t i = node->case_values.size(); i-- > 0;) {
    Expr* matches = conditions_.Never();
    for (Expr* value : node->case_values[i]) {
      auto* eq = arena_.Create<Expr>();
      eq->kind = ExprKind::kBinary;
      eq->op = TokenKind::kEqEqEq;
      eq->lhs = selector;
      eq->rhs = scope.rewrite(value);
      reads.push_back(eq->rhs);
      matches = conditions_.Or(matches, eq);
    }
    if (matches != conditions_.Never()) {
      result = Over(Kind::kIf, {items[i], result}, matches, 0, clock);
    }
  }
  return result;
}

const ObligationNode* AssumeObligations::Build(const PropertyExprNode* node,
                                               int clock,
                                               const ObligationScope& scope,
                                               std::vector<Expr*>& reads) {
  using P = PropertyExprNode::Kind;
  int own = NumberClock(node->clock, clock, scope.rewrite, scope.clocks);
  if (node->kind == P::kBoolean) {
    return BuildBool(node->boolean, own, scope, reads);
  }
  int clock_out = own;
  if (node->kind == P::kSequence) {
    return BuildSequence(node->sequence, own, scope, reads, clock_out);
  }
  if (node->kind == P::kImplication) {
    return BuildImplication(node, own, scope, reads);
  }
  std::vector<const ObligationNode*> ops;
  if (!BuildOperands(node, own, scope, reads, ops)) return nullptr;
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
                  std::move(ops), nullptr, 0, own);
    case P::kNexttime:
    case P::kAlways:
    case P::kEventually:
      return BuildRange(node, ops[0], own, scope);
    case P::kCase:
      return BuildCase(node, ops, own, scope, reads);
    default:
      return BuildConditional(node, std::move(ops), own, scope, reads);
  }
}

// §16.12.6 and §16.12.14: an if-else, its else holding where none was
// written, and an abort, over the condition they read.
const ObligationNode* AssumeObligations::BuildConditional(
    const PropertyExprNode* node, std::vector<const ObligationNode*> ops,
    int clock, const ObligationScope& scope, std::vector<Expr*>& reads) {
  Expr* cond = scope.rewrite(node->boolean);
  reads.push_back(cond);
  if (node->kind == PropertyExprNode::Kind::kIfElse) {
    return Over(Kind::kIf, {ops[0], ops.size() > 1 ? ops[1] : true_}, cond, 0,
                clock);
  }
  return Over(node->accept ? Kind::kAccept : Kind::kReject, std::move(ops),
              cond, 0, clock);
}

// §16.12.7: an implication whose antecedent is a sequence the obligations
// model, overlapping where it is `|->`, its consequent on the clock flowing
// out of the antecedent (§16.13.3).
const ObligationNode* AssumeObligations::BuildImplication(
    const PropertyExprNode* node, int clock, const ObligationScope& scope,
    std::vector<Expr*>& reads) {
  int clock_out = clock;
  const ObligationNode* antecedent =
      BuildSequence(node->sequence, clock, scope, reads, clock_out);
  if (antecedent == nullptr) return nullptr;
  const ObligationNode* consequent =
      Build(node->operands[0], clock_out, scope, reads);
  if (consequent == nullptr) return nullptr;
  return Over(Kind::kImplication, {antecedent, consequent}, nullptr,
              node->strong ? 0 : 1, clock);
}

bool AssumeObligations::Ticked(int clock) const {
  return clock >= kEveryClock || ((ticked_ >> clock) & 1u) != 0;
}

// The condition under which an attempt in one of the sequences `node` holds
// matches at this tick, or, `match` unset, goes on past it.
Expr* AssumeObligations::SeqCondition(const ObligationNode* node, bool match) {
  Expr* any = conditions_.Never();
  for (const SeqTerm* term : node->terms) {
    for (const SeqWay& way : terms_.Ways(term, ticked_, node->fresh)) {
      if ((way.next == nullptr) != match) continue;
      any = conditions_.Or(any, conditions_.AllOf(way.literals));
    }
  }
  return any;
}

// The condition under which `node` does not fail at this tick, or, where
// `decided` is set, under which it holds by this tick and owes nothing
// more.
Expr* AssumeObligations::Condition(const ObligationNode* node, bool decided) {
  uint64_t key =
      (static_cast<uint64_t>(ticked_) << 1) | static_cast<uint64_t>(decided);
  auto found = node->conditions.find(key);
  if (found != node->conditions.end()) return found->second;
  Expr* cond = ConditionOf(node, decided);
  node->conditions[key] = cond;
  return cond;
}

Expr* AssumeObligations::ConditionOf(const ObligationNode* node, bool decided) {
  const auto& ops = node->operands;
  bool conjunction = node->kind == Kind::kAnd;
  Expr* all = conjunction ? conditions_.Always() : conditions_.Never();
  // §16.13: an operand whose clock has not ticked is not read yet, so it
  // neither fails nor holds.
  Expr* pending = decided ? conditions_.Never() : conditions_.Always();
  Expr* own = Ticked(node->clock) ? node->expr : conditions_.Never();
  std::vector<Expr*> reads;
  switch (node->kind) {
    case Kind::kBool:
      return Ticked(node->clock) ? node->expr : pending;
    case Kind::kSeq:
      return conditions_.Or(SeqCondition(node, true),
                            decided ? pending : SeqCondition(node, false));
    case Kind::kNot:
      return conditions_.Not(Condition(ops[0], !decided));
    case Kind::kAnd:
    case Kind::kOr:
      for (const ObligationNode* op : ops) {
        all = conditions_.Join(all, Condition(op, decided), conjunction);
      }
      return all;
    case Kind::kIf:
      if (!Ticked(node->clock)) return pending;
      return conditions_.Or(
          conditions_.And(node->expr, Condition(ops[0], decided)),
          conditions_.And(conditions_.Not(node->expr),
                          Condition(ops[1], decided)));
    case Kind::kNext:
      return pending;
    case Kind::kImplication:
      return ImplicationCondition(node, decided);
    case Kind::kAccept:
      return conditions_.Or(own, Condition(ops[0], decided));
    case Kind::kReject:
      return conditions_.And(conditions_.Not(own), Condition(ops[0], decided));
    case Kind::kInstance:
      Expansion(node, reads);
      return Condition(node->expansion, decided);
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
  Expr* begun = Condition(
      node->n != 0 ? consequent : Next(1, consequent, node->clock), decided);
  Expr* now =
      conditions_.Or(conditions_.Not(SeqCondition(antecedent, true)), begun);
  if (!decided) return now;
  return conditions_.And(conditions_.Not(SeqCondition(antecedent, false)), now);
}

Expr* AssumeObligations::NoFailCondition(const ObligationNode* node,
                                         uint32_t ticked) {
  ticked_ = ticked;
  Expr* cond = Condition(node, false);
  return cond == conditions_.Always() ? nullptr : cond;
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

// The ways of the sequences `node` holds taken at this tick, `next`
// collecting the terms they go on in; true where one matches.
bool AssumeObligations::StepSeq(const ObligationNode* node,
                                std::vector<const SeqTerm*>& next) {
  bool matched = false;
  for (const SeqTerm* term : node->terms) {
    for (const SeqWay& way : terms_.Ways(term, ticked_, node->fresh)) {
      bool taken = std::ranges::all_of(way.literals, [&](const auto& lit) {
        return Holds(lit.first) == lit.second;
      });
      if (!taken) continue;
      if (way.next == nullptr) {
        matched = true;
      } else {
        next.push_back(terms_.Take(way));
      }
    }
  }
  return matched;
}

const ObligationNode* AssumeObligations::Step(const ObligationNode* node,
                                              uint32_t ticked) {
  ticked_ = ticked;
  return StepNode(node);
}

const ObligationNode* AssumeObligations::StepNode(const ObligationNode* node) {
  auto key = std::make_pair(node, ticked_);
  auto found = stepped_.find(key);
  if (found != stepped_.end()) return found->second;
  const ObligationNode* result = StepOperator(node);
  stepped_[key] = result;
  return result;
}

const ObligationNode* AssumeObligations::StepOperator(
    const ObligationNode* node) {
  const auto& ops = node->operands;
  std::vector<const SeqTerm*> next;
  std::vector<const ObligationNode*> stepped;
  std::vector<Expr*> reads;
  bool ticked = Ticked(node->clock);
  switch (node->kind) {
    case Kind::kBool:
      if (!ticked) return node;
      return Holds(node->expr) ? true_ : false_;
    case Kind::kSeq:
      return StepSeq(node, next) ? true_ : Seq(std::move(next), false);
    case Kind::kNot:
      return Not(StepNode(ops[0]));
    case Kind::kAnd:
    case Kind::kOr:
      stepped.reserve(ops.size());
      for (const ObligationNode* op : ops) stepped.push_back(StepNode(op));
      return Junction(node->kind, stepped);
    case Kind::kIf:
      if (!ticked) return node;
      return StepNode(ops[Holds(node->expr) ? 0 : 1]);
    case Kind::kNext:
      if (!ticked) return node;
      return Next(node->n - 1, ops[0], node->clock);
    case Kind::kImplication:
      return StepImplication(node);
    case Kind::kAccept:
    case Kind::kReject:
      return StepAbort(node);
    case Kind::kInstance:
      Expansion(node, reads);
      return StepNode(node->expansion);
    default:
      return StepNode(Expand(node));
  }
}

// §16.12.7: each match of the antecedent at this tick begins an attempt of
// the consequent, at this tick for `|->` and the next for `|=>`, and the
// antecedent goes on while it can match again.
const ObligationNode* AssumeObligations::StepImplication(
    const ObligationNode* node) {
  const ObligationNode* consequent = node->operands[1];
  std::vector<const SeqTerm*> next;
  const ObligationNode* begun = true_;
  if (StepSeq(node->operands[0], next)) {
    begun = node->n != 0 ? StepNode(consequent) : consequent;
  }
  const ObligationNode* rest = true_;
  if (!next.empty()) {
    rest = Over(Kind::kImplication, {Seq(std::move(next), false), consequent},
                nullptr, node->n, node->clock);
  }
  return Junction(Kind::kAnd, {begun, rest});
}

// §16.12.14: an abort whose condition holds at a tick of its clock decides
// the property, accept_on as holding and reject_on as failing; otherwise
// its operand goes on under it.
const ObligationNode* AssumeObligations::StepAbort(const ObligationNode* node) {
  const ObligationNode* aborted = node->kind == Kind::kAccept ? true_ : false_;
  if (Ticked(node->clock) && Holds(node->expr)) return aborted;
  const ObligationNode* operand = StepNode(node->operands[0]);
  if (Settled(operand)) return operand;
  return Over(node->kind, {operand}, node->expr, 0, node->clock);
}

}  // namespace delta
