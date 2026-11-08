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
#include "simulator/sequence_locals.h"
#include "simulator/sim_context.h"

namespace delta {

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
  kLocals,
};

struct ObligationNode {
  ObligationKind kind = ObligationKind::kBool;
  Expr* expr = nullptr;
  uint32_t n = 0;
  int clock = 0;
  bool fresh = false;
  std::vector<const ObligationNode*> operands;
  std::vector<const SeqTerm*> terms;
  const ModuleItem* decl = nullptr;
  const ObligationScope* scope = nullptr;
  const ObligationScope* outer = nullptr;
  const LocalValues* locals = nullptr;
  mutable std::map<uint64_t, Expr*> conditions;
  mutable const ObligationNode* expansion = nullptr;
};

namespace {

using Kind = ObligationKind;

constexpr int kEveryClock = 32;

std::string Id(const void* p) {
  return std::to_string(reinterpret_cast<uintptr_t>(p));
}

std::string KeyOf(const ObligationNode& node) {
  std::string key =
      std::to_string(static_cast<int>(node.kind)) + ':' + Id(node.expr) + ':' +
      std::to_string(node.n) + ':' + std::to_string(node.clock) + ':' +
      std::to_string(static_cast<int>(node.fresh)) + ':' + Id(node.decl) + ':' +
      Id(node.scope) + ':' + Id(node.locals);
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

const ObligationNode* AssumeObligations::WithLocals(
    const LocalValues* locals, const ObligationNode* inner) {
  if (Settled(inner)) return inner;
  ObligationNode node;
  node.kind = Kind::kLocals;
  node.operands = {inner};
  node.locals = locals;
  return Intern(std::move(node));
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
  if (!decl->prop_locals.empty()) {
    built =
        WithLocals(terms_.Locals(InitialLocals(decl->prop_locals, ctx_, arena_),
                                 &decl->prop_locals),
                   built);
  }
  node->expansion = built;
  return built;
}

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
  if (!body->assert_negated) return node;
  return Not(node);
}

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

const ObligationNode* AssumeObligations::BuildInstance(
    Expr* e, const ModuleItem* decl, int clock, const ObligationScope& scope,
    std::vector<Expr*>& reads) {
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
  if (expanding_.count(decl) == 0) Expansion(instance, reads);
  return instance;
}

const ObligationNode* AssumeObligations::BuildSequence(
    const ModuleItem* item, int clock, const ObligationScope& scope,
    std::vector<Expr*>& reads, int& clock_out) {
  const SeqTerm* term = terms_.Begin(item, clock, scope, reads, clock_out);
  if (term == nullptr) return true_;
  return Seq({term}, true);
}

void AssumeObligations::BuildOperands(const PropertyExprNode* node, int clock,
                                      const ObligationScope& scope,
                                      std::vector<Expr*>& reads,
                                      std::vector<const ObligationNode*>& out) {
  for (const PropertyExprNode* operand : node->operands) {
    out.push_back(Build(operand, clock, scope, reads));
  }
}

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
  BuildOperands(node, own, scope, reads, ops);
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

const ObligationNode* AssumeObligations::BuildImplication(
    const PropertyExprNode* node, int clock, const ObligationScope& scope,
    std::vector<Expr*>& reads) {
  int clock_out = clock;
  const ObligationNode* antecedent =
      BuildSequence(node->sequence, clock, scope, reads, clock_out);
  const ObligationNode* consequent =
      Build(node->operands[0], clock_out, scope, reads);
  return Over(Kind::kImplication, {antecedent, consequent}, nullptr,
              node->strong ? 0 : 1, clock);
}

bool AssumeObligations::Ticked(int clock) const {
  return clock >= kEveryClock || ((ticked_ >> clock) & 1u) != 0;
}

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
    case Kind::kLocals:
      return UnderLocals(Condition(ops[0], decided), node->locals);
    default:
      return Condition(Expand(node), decided);
  }
}

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
  for (auto frame = frames_.rbegin(); frame != frames_.rend(); ++frame) {
    e = SubstituteFormals(e, frame->first->references, arena_);
  }
  auto found = values_.find(e);
  if (found != values_.end()) return found->second;
  ctx_.PushScope();
  terms_.BindLocalsOf(e);
  bool value = EvalExpr(e, ctx_, arena_).IsTruthy();
  ctx_.PopScope();
  values_[e] = value;
  return value;
}

bool AssumeObligations::Settled(const ObligationNode* node) const {
  return node == true_ || node == false_;
}

bool AssumeObligations::StepSeq(const ObligationNode* node,
                                std::vector<const SeqTerm*>& next) {
  bool matched = false;
  for (const SeqTerm* term : node->terms) {
    for (const SeqWay& way : terms_.Ways(term, ticked_, node->fresh)) {
      bool taken = std::ranges::all_of(way.literals, [&](const auto& lit) {
        return Holds(lit.first) == lit.second;
      });
      if (!taken) continue;
      for (auto& frame : frames_) {
        PerformMatchItems(way.items, frame.second, ctx_, arena_);
      }
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
  if (!frames_.empty()) return StepOperator(node);
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
    case Kind::kLocals:
      return StepLocals(node);
    default:
      return StepNode(Expand(node));
  }
}

const ObligationNode* AssumeObligations::StepLocals(
    const ObligationNode* node) {
  frames_.emplace_back(node->locals, *node->locals);
  const ObligationNode* inner = StepNode(node->operands[0]);
  LocalValues after = std::move(frames_.back().second);
  frames_.pop_back();
  return WithLocals(terms_.Locals(std::move(after.values), after.decls), inner);
}

Expr* AssumeObligations::UnderLocals(Expr* cond, const LocalValues* locals) {
  if (cond == conditions_.Always()) return cond;
  return SubstituteFormals(cond, locals->references, arena_);
}

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

const ObligationNode* AssumeObligations::StepAbort(const ObligationNode* node) {
  const ObligationNode* aborted = node->kind == Kind::kAccept ? true_ : false_;
  if (Ticked(node->clock) && Holds(node->expr)) return aborted;
  const ObligationNode* operand = StepNode(node->operands[0]);
  if (Settled(operand)) return operand;
  return Over(node->kind, {operand}, node->expr, 0, node->clock);
}

}  // namespace delta
