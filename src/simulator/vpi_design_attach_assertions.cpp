#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.50: the object kind of the concurrent assertion `item` writes, by its
// keyword.
int ConcurrentKindOf(const ModuleItem& item) {
  switch (item.kind) {
    case ModuleItemKind::kAssumeProperty:
      return vpiAssume;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      return vpiCover;
    case ModuleItemKind::kRestrictProperty:
      return vpiRestrict;
    default:
      return vpiAssert;
  }
}

// §37.50: the object the concurrent assertion `item` stands as in `scope`,
// named by its label, reporting where it stands and, for a cover, whether it
// covers a sequence.
VpiObject* MakeConcurrentAssertion(const ModuleItem& item, VpiObject* scope,
                                   SimContext& ctx,
                                   const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = ConcurrentKindOf(item);
  obj->parent = scope;
  if (!item.name.empty()) {
    obj->name = build.keep(std::string(item.name));
    obj->full_name = VpiScopedFullName(scope, item.name);
  }
  obj->cover_sequence = item.kind == ModuleItemKind::kCoverSequence;
  VpiRecordAssertionLocation(obj, SourceRange{item.loc, item.end}, ctx);
  scope->children.push_back(obj);
  return obj;
}

// §37.52 detail 2: the operation of `op_type` over `operands`, in the order
// given, strong where `strong` is (detail 3); null where an operand is.
VpiObject* PropertyOperation(int op_type,
                             const std::vector<VpiObject*>& operands,
                             bool strong, const VpiAttachBuild& build) {
  for (const VpiObject* operand : operands) {
    if (operand == nullptr) return nullptr;
  }
  VpiObject* op = build.alloc();
  op->type = vpiOperation;
  op->op_type = op_type;
  op->op_strong = strong;
  op->children = operands;
  return op;
}

// §37.54 detail 3: the bound `value` of a range or a repetition, `$` the
// unbounded constant.
VpiObject* BoundConstant(uint32_t value, const VpiAttachBuild& build) {
  if (value != SeqCycleDelay::kUnbounded) return VpiIntConstant(value, build);
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = vpiUnboundedConst;
  return constant;
}

// §37.54 detail 3: the left bound `min` onto `operands`, and the right bound
// `max` where it differs from the left.
void AppendBounds(std::vector<VpiObject*>& operands, uint32_t min, uint32_t max,
                  const VpiAttachBuild& build) {
  operands.push_back(BoundConstant(min, build));
  if (max != min) operands.push_back(BoundConstant(max, build));
}

// §16.10 and §16.11: the match item `item` written with an operand of a
// sequence, hung from `holder`: a tf call as the call it is, and an assignment
// to the local variable it names with its operator (§37.64).
VpiObject* MatchItemObject(const SeqMatchAssign& item, VpiObject* holder,
                           const VpiStmtBuild& with) {
  if (item.call != nullptr) return with.expression(item.call);
  VpiObject* assignment = with.build.alloc();
  assignment->type = vpiAssignment;
  assignment->parent = holder;
  VpiObject* local = with.build.alloc();
  local->type = vpiRefObj;
  local->parent = assignment;
  local->name = with.build.keep(std::string(item.lvar));
  assignment->lhs = local;
  assignment->rhs = with.expression(item.rhs);
  std::string_view spelling = TokenKindName(item.op);
  if (spelling.size() >= 2 && spelling.front() == '\'' &&
      spelling.back() == '\'') {
    spelling = spelling.substr(1, spelling.size() - 2);
  }
  assignment->op_type = VpiAssignmentOpType(spelling);
  assignment->blocking = true;
  return assignment;
}

// §37.54: the operand `object` reaching the match items `items` through
// vpiMatchItem: itself where it is an expression of its own, and otherwise a
// ref obj bound to the net or variable it names (§37.15), which other
// references to that object share.
VpiObject* WithMatchItems(VpiObject* object,
                          const std::vector<SeqMatchAssign>& items,
                          const VpiStmtBuild& with) {
  if (object == nullptr || items.empty()) return object;
  VpiObject* holder = object;
  if (!VpiIsExprType(object->type)) {
    holder = with.build.alloc();
    holder->type = vpiRefObj;
    holder->name = object->name;
    holder->full_name = object->full_name;
    holder->actual = object;
  }
  for (const SeqMatchAssign& item : items) {
    VpiObject* made = MatchItemObject(item, holder, with);
    if (made != nullptr) holder->children.push_back(made);
  }
  return holder;
}

// §16.9.2: the operand `index` of the chain `body` with its match items,
// under the repetition it carries, the sequence repeated first and then its
// bounds (detail 3).
VpiObject* RepeatedOperand(const SeqLinearBody& body, size_t index,
                           const VpiStmtBuild& with) {
  VpiObject* operand = with.expression(body.operands[index]);
  if (index < body.match_items.size()) {
    operand = WithMatchItems(operand, body.match_items[index], with);
  }
  if (index >= body.repetitions.size()) return operand;
  const SeqRepetition& repetition = body.repetitions[index];
  int op = vpiRepeatOp;
  switch (repetition.kind) {
    case SeqRepetition::Kind::kNone:
      return operand;
    case SeqRepetition::Kind::kConsecutive:
      op = vpiConsecutiveRepeatOp;
      break;
    case SeqRepetition::Kind::kGoto:
      op = vpiGotoRepeatOp;
      break;
    default:
      break;
  }
  std::vector<VpiObject*> operands{operand};
  AppendBounds(operands, repetition.min, repetition.max, with.build);
  return PropertyOperation(op, operands, false, with.build);
}

// One element of a chain: the delay written before it and the sequence it
// is, an operand or a throughout over a span of operands.
struct ChainElement {
  SeqCycleDelay before;
  VpiObject* sequence = nullptr;
};

// §16.9.1 and §16.9.2: `elements` joined left to right by the cycle delays
// between them, each with its two sequences and its range, and a delay
// before the first a unary cycle delay over it (detail 3).
VpiObject* JoinChain(const std::vector<ChainElement>& elements,
                     const VpiStmtBuild& with) {
  if (elements.empty()) return nullptr;
  VpiObject* chain = elements[0].sequence;
  const SeqCycleDelay& lead = elements[0].before;
  if (lead.min != 0 || lead.max != 0) {
    std::vector<VpiObject*> operands{chain};
    AppendBounds(operands, lead.min, lead.max, with.build);
    chain =
        PropertyOperation(vpiUnaryCycleDelayOp, operands, false, with.build);
  }
  for (size_t i = 1; i < elements.size(); ++i) {
    std::vector<VpiObject*> operands{chain, elements[i].sequence};
    AppendBounds(operands, elements[i].before.min, elements[i].before.max,
                 with.build);
    chain = PropertyOperation(vpiCycleDelayOp, operands, false, with.build);
  }
  return chain;
}

// §16.9.9: the widest throughout of `body` other than `inside` whose span
// starts at the operand `index` and ends before `end`; null where none does.
const SeqThroughout* ThroughoutAt(const SeqLinearBody& body, size_t index,
                                  size_t end, const SeqThroughout* inside) {
  const SeqThroughout* widest = nullptr;
  for (const SeqThroughout& span : body.throughouts) {
    if (&span == inside || span.first != index || span.last >= end) continue;
    if (widest == nullptr || span.last > widest->last) widest = &span;
  }
  return widest;
}

// `delay` with `ticks` taken off both its bounds, an unbounded one kept.
SeqCycleDelay Shortened(SeqCycleDelay delay, uint32_t ticks) {
  delay.min -= std::min(ticks, delay.min);
  if (delay.max != SeqCycleDelay::kUnbounded) {
    delay.max -= std::min(ticks, delay.max);
  }
  return delay;
}

std::vector<ChainElement> ChainElements(const SeqLinearBody& body, size_t begin,
                                        size_t end, const SeqThroughout* inside,
                                        const VpiStmtBuild& with);

// §16.9.9: `span` as the throughout written, its condition and the sequence
// its operands are, that sequence's own leading delay `lead` ticks.
VpiObject* ThroughoutExpr(const SeqLinearBody& body, const SeqThroughout& span,
                          const VpiStmtBuild& with) {
  std::vector<ChainElement> held =
      ChainElements(body, span.first, span.last + 1, &span, with);
  if (!held.empty()) {
    held[0].before.min = span.lead;
    held[0].before.max = span.lead;
  }
  return PropertyOperation(vpiThroughoutOp,
                           {with.expression(span.cond), JoinChain(held, with)},
                           false, with.build);
}

// The elements the operands of `body` from `begin` to before `end` make, a
// throughout's span other than `inside` one element of its own (§16.9.9).
std::vector<ChainElement> ChainElements(const SeqLinearBody& body, size_t begin,
                                        size_t end, const SeqThroughout* inside,
                                        const VpiStmtBuild& with) {
  std::vector<ChainElement> elements;
  for (size_t i = begin; i < end;) {
    const SeqCycleDelay kBefore =
        i < body.delays.size() ? body.delays[i] : SeqCycleDelay{};
    const SeqThroughout* span = ThroughoutAt(body, i, end, inside);
    if (span == nullptr) {
      elements.push_back({kBefore, RepeatedOperand(body, i, with)});
      ++i;
      continue;
    }
    elements.push_back(
        {Shortened(kBefore, span->lead), ThroughoutExpr(body, *span, with)});
    i = span->last + 1;
  }
  return elements;
}

// §16.9.1: the chain `body` as the sequence expr its operands make.
VpiObject* ChainExpr(const SeqLinearBody& body, const VpiStmtBuild& with) {
  return JoinChain(ChainElements(body, 0, body.operands.size(), nullptr, with),
                   with);
}

// §16.9.10: the chain `body` wraps the first operand of a within as
// `1[*0:$] ##1 seq1 ##1 1[*0:$]`; the chain seq1 was, the wrapping taken off.
SeqLinearBody UnwrappedWithin(const SeqLinearBody& body) {
  SeqLinearBody inner;
  const size_t kLast = body.operands.size() - 1;
  for (size_t i = 1; i < kLast; ++i) {
    inner.operands.push_back(body.operands[i]);
    inner.delays.push_back(i == 1 ? Shortened(body.delays[i], 1)
                                  : body.delays[i]);
    inner.match_items.push_back(body.match_items[i]);
    inner.repetitions.push_back(body.repetitions[i]);
  }
  for (SeqThroughout span : body.throughouts) {
    span.first -= 1;
    span.last -= 1;
    inner.throughouts.push_back(span);
  }
  return inner;
}

// §16.9.5, §16.9.6 and §16.9.10: the chain `body`, or the within it is the
// first operand of, intersected with each further chain of its intersect,
// the whole and-ed with each of its conjuncts, left to right.
VpiObject* ConjunctionExpr(const SeqLinearBody& body,
                           const VpiStmtBuild& with) {
  const bool kWithin =
      body.within && body.operands.size() >= 3 && !body.intersects.empty();
  VpiObject* joined =
      kWithin ? PropertyOperation(vpiWithinOp,
                                  {ChainExpr(UnwrappedWithin(body), with),
                                   ChainExpr(body.intersects.front(), with)},
                                  false, with.build)
              : ChainExpr(body, with);
  for (size_t i = kWithin ? 1 : 0; i < body.intersects.size(); ++i) {
    joined = PropertyOperation(vpiIntersectOp,
                               {joined, ChainExpr(body.intersects[i], with)},
                               false, with.build);
  }
  for (const SeqLinearBody& other : body.conjuncts) {
    joined =
        PropertyOperation(vpiCompAndOp, {joined, ConjunctionExpr(other, with)},
                          false, with.build);
  }
  return joined;
}

// Whether every part of `body` is one the sequence exprs below are built of:
// no operand with a clocking event of its own (§37.56) and no match item
// written inside a first_match.
bool IsModelledSequence(const SeqLinearBody& body) {
  const auto kUnclocked = [](const std::vector<EventExpr>& clock) {
    return clock.empty();
  };
  if (!body.first_match_items.empty() ||
      !std::ranges::all_of(body.clocks, kUnclocked)) {
    return false;
  }
  for (const auto* parts :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    if (!std::ranges::all_of(*parts, IsModelledSequence)) return false;
  }
  return true;
}

// §37.52 with §37.54: the sequence `sequence` as a property expr or as an
// operand of a property operator, the clock `flowing` into it (§16.13.3);
// null for one holding a part not built.
VpiObject* SequenceOperand(const ModuleItem* sequence, const VpiStmtBuild& with,
                           const std::vector<EventExpr>* flowing) {
  if (sequence == nullptr) return nullptr;
  return VpiSequenceExprObject(sequence->seq_linear, with, flowing);
}

// §16.13.3: the clock flowing into the consequent of an implication whose
// antecedent is `antecedent`, the clock `flowing` into the implication: the
// one in force at the antecedent's end where the antecedent names clocks
// outside parentheses and instances.
const std::vector<EventExpr>* ConsequentClock(
    const ModuleItem* antecedent, const std::vector<EventExpr>* flowing) {
  if (antecedent == nullptr || antecedent->seq_linear.clocks.empty() ||
      antecedent->seq_linear.clock_out.empty()) {
    return flowing;
  }
  return &antecedent->seq_linear.clock_out;
}

// Whether `body` is one chain and nothing beside it, an operand of an
// intersect, an and, an or or a first_match standing apart from its clocks.
bool IsLoneChain(const SeqLinearBody& body) {
  return body.intersects.empty() && body.conjuncts.empty() &&
         body.alternatives.empty() && !body.first_match;
}

// §37.56: the clocked seq of the operands of `body` from `start` to before
// `end`, on `clock`, reaching it and the sequence expr they are, a run after
// the first joined to the one before by the clock change rather than a delay.
VpiObject* ClockedRun(const SeqLinearBody& body, size_t start, size_t end,
                      const std::vector<EventExpr>* clock,
                      const VpiStmtBuild& with) {
  std::vector<ChainElement> run =
      ChainElements(body, start, end, nullptr, with);
  if (start > 0 && !run.empty()) {
    run[0].before.min = 0;
    run[0].before.max = 0;
  }
  VpiObject* clocked = with.build.alloc();
  clocked->type = vpiClockedSeq;
  if (clock != nullptr) {
    clocked->clocking_event = VpiEventCondition(*clock, with);
  }
  VpiObject* sequence = JoinChain(run, with);
  if (sequence != nullptr) clocked->children.push_back(sequence);
  return clocked;
}

// §16.13.1: whether a clock is written before the operand `i` of `body`, the
// operands after it carrying the same event as the clock in force.
bool ClockWrittenAt(const SeqLinearBody& body, size_t i) {
  if (i >= body.clocks.size() || body.clocks[i].empty()) return false;
  return i == 0 || body.clocks[i - 1].empty() ||
         body.clocks[i - 1][0].signal != body.clocks[i][0].signal;
}

// §37.56 with §16.13.1: the chain `body`, whose operands name clocks of their
// own, as a multiclock sequence expr reaching a clocked seq per run of
// operands on one clock, the first run's the clock `flowing` into the chain
// where it names none.
VpiObject* MulticlockExpr(const SeqLinearBody& body,
                          const std::vector<EventExpr>* flowing,
                          const VpiStmtBuild& with) {
  VpiObject* multiclock = with.build.alloc();
  multiclock->type = vpiMulticlockSequenceExpr;
  const size_t kCount = body.operands.size();
  const auto kClockAt = [&body](size_t i) -> const std::vector<EventExpr>* {
    return i < body.clocks.size() && !body.clocks[i].empty() ? &body.clocks[i]
                                                             : nullptr;
  };
  for (size_t start = 0; start < kCount;) {
    size_t end = start + 1;
    while (end < kCount && !ClockWrittenAt(body, end)) ++end;
    const std::vector<EventExpr>* clock =
        kClockAt(start) != nullptr ? kClockAt(start) : flowing;
    VpiObject* clocked = ClockedRun(body, start, end, clock, with);
    clocked->parent = multiclock;
    multiclock->children.push_back(clocked);
    start = end;
  }
  return multiclock;
}

// The property expr of the operand `index` of `node`, the clock `flowing`
// into it; null where it has none.
VpiObject* OperandOf(const PropertyExprNode& node, size_t index,
                     const VpiStmtBuild& with,
                     const std::vector<EventExpr>* flowing) {
  return index < node.operands.size()
             ? VpiPropertyExprObject(node.operands[index], with, flowing)
             : nullptr;
}

// §16.12.5: an and or an or over every operand of `node`, joined left to
// right as the grammar's binary operator joins them.
VpiObject* JoinedOperation(int op_type, const PropertyExprNode& node,
                           const VpiStmtBuild& with,
                           const std::vector<EventExpr>* flowing) {
  VpiObject* joined = OperandOf(node, 0, with, flowing);
  for (size_t i = 1; i < node.operands.size(); ++i) {
    joined =
        PropertyOperation(op_type, {joined, OperandOf(node, i, with, flowing)},
                          false, with.build);
  }
  return joined;
}

// §16.12.9: the followed-by `node`, the not standing for it, as the operator
// written: the implication's antecedent, then the property its negated
// consequent negates.
VpiObject* FollowedByOperation(const PropertyExprNode& node,
                               const VpiStmtBuild& with,
                               const std::vector<EventExpr>* flowing) {
  const PropertyExprNode* implication =
      node.operands.empty() ? nullptr : node.operands.front();
  if (implication == nullptr || implication->operands.empty() ||
      implication->operands.front()->operands.empty()) {
    return nullptr;
  }
  const int kOp =
      implication->strong ? vpiNonOverlapFollowedByOp : vpiOverlapFollowedByOp;
  return PropertyOperation(
      kOp,
      {SequenceOperand(implication->sequence, with, flowing),
       OperandOf(*implication->operands.front(), 0, with,
                 ConsequentClock(implication->sequence, flowing))},
      false, with.build);
}

// §16.12.10: an if, or an if-else where an else is written, its condition
// first.
VpiObject* ConditionalOperation(const PropertyExprNode& node,
                                const VpiStmtBuild& with,
                                const std::vector<EventExpr>* flowing) {
  std::vector<VpiObject*> operands{with.expression(node.boolean),
                                   OperandOf(node, 0, with, flowing)};
  if (node.operands.size() > 1) {
    operands.push_back(OperandOf(node, 1, with, flowing));
  }
  return PropertyOperation(node.operands.size() > 1 ? vpiIfElseOp : vpiIfOp,
                           operands, false, with.build);
}

// §16.12.11 and §16.12.13 with detail 2: a nexttime takes its property and
// its constant, the constant only where it is other than 1; an always and an
// eventually their property and the bounds of their range.
VpiObject* CountedOperation(int op_type, const PropertyExprNode& node,
                            const VpiStmtBuild& with,
                            const std::vector<EventExpr>* flowing) {
  VpiObject* property = OperandOf(node, 0, with, flowing);
  if (op_type == vpiNexttimeOp) {
    const Expr* count = node.boolean;
    const bool kOne = count != nullptr &&
                      count->kind == ExprKind::kIntegerLiteral &&
                      count->int_val == 1;
    return PropertyOperation(
        op_type, VpiNexttimeOperands(property, with.expression(count), !kOne),
        node.strong, with.build);
  }
  return PropertyOperation(
      op_type,
      VpiAlwaysEventuallyOperands(property, with.expression(node.range_min),
                                  with.expression(node.range_max)),
      node.strong, with.build);
}

// §16.12.3 and §16.12.9: a not over its operand, or the followed-by it
// stands for.
VpiObject* NotOperation(const PropertyExprNode& node, const VpiStmtBuild& with,
                        const std::vector<EventExpr>* flowing) {
  if (node.followed_by) return FollowedByOperation(node, with, flowing);
  return PropertyOperation(vpiNotOp, {OperandOf(node, 0, with, flowing)}, false,
                           with.build);
}

// §16.12.7: an implication, overlapping or not, its antecedent first, the
// clock `flowing` into it flowing on across it (§16.13.3).
VpiObject* ImplicationOperation(const PropertyExprNode& node,
                                const VpiStmtBuild& with,
                                const std::vector<EventExpr>* flowing) {
  const int kOp = node.strong ? vpiNonOverlapImplyOp : vpiOverlapImplyOp;
  return PropertyOperation(
      kOp,
      {SequenceOperand(node.sequence, with, flowing),
       OperandOf(node, 0, with, ConsequentClock(node.sequence, flowing))},
      false, with.build);
}

// §16.12.8 and §16.12.12: the operator of an implies, an iff or an until,
// the untils told apart by whether they overlap.
int BinaryOp(const PropertyExprNode& node) {
  switch (node.kind) {
    case PropertyExprNode::Kind::kImplies:
      return vpiImpliesOp;
    case PropertyExprNode::Kind::kIff:
      return vpiIffOp;
    default:
      return node.range_unbounded ? vpiUntilWithOp : vpiUntilOp;
  }
}

// §16.12.8 and §16.12.12: an implies, an iff or an until over its two
// operands, an until strong where it was written so.
VpiObject* BinaryOperation(const PropertyExprNode& node,
                           const VpiStmtBuild& with,
                           const std::vector<EventExpr>* flowing) {
  return PropertyOperation(
      BinaryOp(node),
      {OperandOf(node, 0, with, flowing), OperandOf(node, 1, with, flowing)},
      node.strong, with.build);
}

// §16.12.14: the abort operator `node` was written with.
int AbortOp(const PropertyExprNode& node) {
  if (node.accept) return node.synchronous ? vpiSyncAcceptOnOp : vpiAcceptOnOp;
  return node.synchronous ? vpiSyncRejectOnOp : vpiRejectOnOp;
}

// §37.52 with §16.12.16: the case property `node`, reaching its case
// expression through vpiCondition and an item per property it branches to,
// each grouping the expressions written before that property (detail 4),
// the default's none (detail 5).
VpiObject* CaseProperty(const PropertyExprNode& node, const VpiStmtBuild& with,
                        const std::vector<EventExpr>* flowing) {
  VpiObject* obj = with.build.alloc();
  obj->type = vpiCaseProperty;
  VpiObject* condition = with.expression(node.boolean);
  if (condition != nullptr) obj->children.push_back(condition);
  for (size_t i = 0; i < node.operands.size(); ++i) {
    VpiObject* item = with.build.alloc();
    item->type = vpiCasePropertyItem;
    item->parent = obj;
    if (i < node.case_values.size()) {
      for (const Expr* value : node.case_values[i]) {
        VpiObject* expression = with.expression(value);
        if (expression != nullptr) item->children.push_back(expression);
      }
    }
    item->body = OperandOf(node, i, with, flowing);
    obj->children.push_back(item);
  }
  return obj;
}

// §37.52: the property expr `node` stands for, its own clock aside, the
// clock `flowing` into it flowing into its operands (§16.13.3).
VpiObject* UnclockedPropertyExpr(const PropertyExprNode* node,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing) {
  using Kind = PropertyExprNode::Kind;
  switch (node->kind) {
    case Kind::kBoolean:
      return with.expression(node->boolean);
    case Kind::kSequence:
      return SequenceOperand(node->sequence, with, flowing);
    case Kind::kNot:
      return NotOperation(*node, with, flowing);
    case Kind::kOr:
      return JoinedOperation(vpiCompOrOp, *node, with, flowing);
    case Kind::kAnd:
      return JoinedOperation(vpiCompAndOp, *node, with, flowing);
    case Kind::kIfElse:
      return ConditionalOperation(*node, with, flowing);
    case Kind::kImplication:
      return ImplicationOperation(*node, with, flowing);
    case Kind::kImplies:
    case Kind::kIff:
    case Kind::kUntil:
      return BinaryOperation(*node, with, flowing);
    case Kind::kNexttime:
      return CountedOperation(vpiNexttimeOp, *node, with, flowing);
    case Kind::kAlways:
      return CountedOperation(vpiAlwaysOp, *node, with, flowing);
    case Kind::kEventually:
      return CountedOperation(vpiEventuallyOp, *node, with, flowing);
    case Kind::kAbort:
      return PropertyOperation(
          AbortOp(*node),
          {with.expression(node->boolean), OperandOf(*node, 0, with, flowing)},
          false, with.build);
    case Kind::kCase:
      return CaseProperty(*node, with, flowing);
    default:
      return nullptr;
  }
}

}  // namespace

VpiObject* VpiSequenceExprObject(const SeqLinearBody& body,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing) {
  const auto kUnclocked = [](const std::vector<EventExpr>& clock) {
    return clock.empty();
  };
  if (!std::ranges::all_of(body.clocks, kUnclocked)) {
    return IsLoneChain(body) ? MulticlockExpr(body, flowing, with) : nullptr;
  }
  if (!IsModelledSequence(body)) return nullptr;
  // §16.9.7 and §16.9.8: the alternatives of an or, left to right, and the
  // whole under the first_match it is the operand of.
  VpiObject* whole = ConjunctionExpr(body, with);
  for (const SeqLinearBody& other : body.alternatives) {
    whole = PropertyOperation(
        vpiCompOrOp, {whole, ConjunctionExpr(other, with)}, false, with.build);
  }
  if (body.first_match) {
    whole = PropertyOperation(vpiFirstMatchOp, {whole}, false, with.build);
  }
  return whole;
}

VpiObject* VpiPropertyExprObject(const PropertyExprNode* node,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing) {
  if (node == nullptr) return nullptr;
  // §16.13.3: a clock of the property's own replaces the one flowing in.
  VpiObject* property = UnclockedPropertyExpr(
      node, with, node->clock.empty() ? flowing : &node->clock);
  if (property == nullptr || node->clock.empty()) return property;
  // §37.52 with §16.13.2: a property written under a clocking event of its
  // own is a clocked property, reaching that event and the property.
  VpiObject* clocked = with.build.alloc();
  clocked->type = vpiClockedProp;
  clocked->clocking_event = VpiEventCondition(node->clock, with);
  clocked->children.push_back(property);
  return clocked;
}

void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx) {
  // §37.49: where the assertion stands - its file, the line and column it
  // starts at and those it ends at - read where the text was written (§22.12).
  // A position the parser did not record leaves its pair as it was.
  const SourceManager& sources = ctx.GetDiag().Sources();
  if (range.start.IsValid()) {
    const SourceLoc kStart = sources.ResolveToOrigin(range.start);
    obj->file = std::string(sources.FilePath(kStart.file_id));
    obj->start_line = static_cast<int>(kStart.line);
    obj->column = static_cast<int>(kStart.column);
  }
  if (range.end.IsValid()) {
    const SourceLoc kEnd = sources.ResolveToOrigin(range.end);
    obj->end_line = static_cast<int>(kEnd.line);
    obj->end_column = static_cast<int>(kEnd.column);
  }
}

void VpiMakeItemAssertion(const RtlirAssertion& assertion, VpiObject* scope,
                          SimContext& ctx, const VpiStmtBuild& with) {
  const ModuleItem& item = *assertion.item;
  // §37.49 with §39.3.1 step b: an assertion written as an item is an
  // assertion of the scope writing it. A deferred immediate one runs as a
  // process the elaborator makes of it, whose walk builds it as the statement
  // it is, with its parts (§37.55).
  if (item.body != nullptr && item.body->is_deferred) return;
  VpiObject* obj = MakeConcurrentAssertion(item, scope, ctx, with.build);
  // §37.50: the clock the elaborator resolved onto the statement it carries,
  // where it carries one, and the property: a property inst where the spec
  // instantiates a declared property, a property spec otherwise.
  if (item.body != nullptr) {
    VpiFillAssertionClock(obj, *item.body, with);
    // §16.5.2: a clock of $global_clock is the event this instance's global
    // clocking declaration names (§14.14).
    if (assertion.leading_clock != nullptr) {
      obj->clocking_event = VpiEventCondition(*assertion.leading_clock, with);
    }
  }
  if (!item.prop_instance_name.empty() && item.assert_expr != nullptr) {
    VpiMakePropertyInst(obj, *item.assert_expr, with);
  } else if (item.body != nullptr) {
    VpiMakePropertySpec(obj, *item.body, with);
  }
  // §37.50 detail 2: a restrict writes no action; §16.14.3 gives a cover a
  // pass action alone.
  with.statement(item.assert_pass_stmt, obj);
  obj->else_stmt = with.statement(item.assert_fail_stmt, obj);
}

}  // namespace delta
