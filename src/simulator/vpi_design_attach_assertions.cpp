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
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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

VpiObject* BoundConstant(uint32_t value, const VpiAttachBuild& build) {
  if (value != SeqCycleDelay::kUnbounded) return VpiIntConstant(value, build);
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = vpiUnboundedConst;
  return constant;
}

void AppendBounds(std::vector<VpiObject*>& operands, uint32_t min, uint32_t max,
                  const VpiAttachBuild& build) {
  operands.push_back(BoundConstant(min, build));
  if (max != min) operands.push_back(BoundConstant(max, build));
}

VpiObject* MatchItemLhs(const SeqMatchAssign& item, VpiObject* assignment,
                        const VpiStmtBuild& with) {
  if (item.target != nullptr) return with.expression(item.target);
  VpiObject* local = with.build.alloc();
  local->type = vpiRefObj;
  local->parent = assignment;
  local->name = with.build.keep(std::string(item.lvar));
  return local;
}

VpiObject* MatchItemObject(const SeqMatchAssign& item, VpiObject* holder,
                           const VpiStmtBuild& with) {
  if (item.call != nullptr) return with.expression(item.call);
  VpiObject* assignment = with.build.alloc();
  assignment->type = vpiAssignment;
  assignment->parent = holder;
  assignment->lhs = MatchItemLhs(item, assignment, with);
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

VpiObject* RepeatedOperand(const SeqLinearBody& body, size_t index,
                           const VpiStmtBuild& with) {
  VpiObject* operand = VpiSequenceOperandObject(*body.operands[index], with);
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

struct ChainElement {
  SeqCycleDelay before;
  VpiObject* sequence = nullptr;
};

VpiObject* JoinChain(const std::vector<ChainElement>& elements,
                     const VpiStmtBuild& with) {
  if (elements.empty()) return nullptr;
  VpiObject* chain = elements[0].sequence;
  const SeqCycleDelay& lead = elements[0].before;
  if (lead.min != 0 || lead.max != 0 || lead.written) {
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

const SeqThroughout* ThroughoutAt(const SeqLinearBody& body, size_t index,
                                  size_t end, const SeqThroughout* inside) {
  const SeqThroughout* widest = nullptr;
  for (const SeqThroughout& span : body.throughouts) {
    if (&span == inside || span.first != index || span.last >= end) continue;
    if (widest == nullptr || span.last > widest->last) widest = &span;
  }
  return widest;
}

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

VpiObject* ThroughoutExpr(const SeqLinearBody& body, const SeqThroughout& span,
                          const VpiStmtBuild& with) {
  std::vector<ChainElement> held =
      ChainElements(body, span.first, span.last + 1, &span, with);
  if (!held.empty()) {
    held[0].before.min = span.lead;
    held[0].before.max = span.lead;
    held[0].before.written = false;
  }
  return PropertyOperation(vpiThroughoutOp,
                           {with.expression(span.cond), JoinChain(held, with)},
                           false, with.build);
}

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

VpiObject* ChainExpr(const SeqLinearBody& body, const VpiStmtBuild& with) {
  return JoinChain(ChainElements(body, 0, body.operands.size(), nullptr, with),
                   with);
}

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

VpiObject* SequenceOperand(const ModuleItem* sequence, const VpiStmtBuild& with,
                           const std::vector<EventExpr>* flowing) {
  if (sequence == nullptr) return nullptr;
  return VpiSequenceExprObject(sequence->seq_linear, with, flowing);
}

const std::vector<EventExpr>* ConsequentClock(
    const ModuleItem* antecedent, const std::vector<EventExpr>* flowing) {
  if (antecedent == nullptr || antecedent->seq_linear.clocks.empty() ||
      antecedent->seq_linear.clock_out.empty()) {
    return flowing;
  }
  return &antecedent->seq_linear.clock_out;
}

bool IsLoneChain(const SeqLinearBody& body) {
  return body.intersects.empty() && body.conjuncts.empty() &&
         body.alternatives.empty() && !body.first_match;
}

VpiObject* ClockedRun(const SeqLinearBody& body, size_t start, size_t end,
                      const std::vector<EventExpr>* clock,
                      const VpiStmtBuild& with) {
  std::vector<ChainElement> run =
      ChainElements(body, start, end, nullptr, with);
  if (start > 0 && !run.empty()) {
    run[0].before.min = 0;
    run[0].before.max = 0;
    run[0].before.written = false;
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

bool ClockWrittenAt(const SeqLinearBody& body, size_t i) {
  if (i >= body.clocks.size() || body.clocks[i].empty()) return false;
  return i == 0 || body.clocks[i - 1].empty() ||
         body.clocks[i - 1][0].signal != body.clocks[i][0].signal;
}

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

VpiObject* OperandOf(const PropertyExprNode& node, size_t index,
                     const VpiStmtBuild& with,
                     const std::vector<EventExpr>* flowing) {
  return index < node.operands.size()
             ? VpiPropertyExprObject(node.operands[index], with, flowing)
             : nullptr;
}

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
  VpiObject* right = node.range_min != nullptr && node.range_unbounded
                         ? BoundConstant(SeqCycleDelay::kUnbounded, with.build)
                         : with.expression(node.range_max);
  return PropertyOperation(
      op_type,
      VpiAlwaysEventuallyOperands(property, with.expression(node.range_min),
                                  right),
      node.strong, with.build);
}

VpiObject* NotOperation(const PropertyExprNode& node, const VpiStmtBuild& with,
                        const std::vector<EventExpr>* flowing) {
  if (node.followed_by) return FollowedByOperation(node, with, flowing);
  return PropertyOperation(vpiNotOp, {OperandOf(node, 0, with, flowing)}, false,
                           with.build);
}

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

VpiObject* BinaryOperation(const PropertyExprNode& node,
                           const VpiStmtBuild& with,
                           const std::vector<EventExpr>* flowing) {
  return PropertyOperation(
      BinaryOp(node),
      {OperandOf(node, 0, with, flowing), OperandOf(node, 1, with, flowing)},
      node.strong, with.build);
}

int AbortOp(const PropertyExprNode& node) {
  if (node.accept) return node.synchronous ? vpiSyncAcceptOnOp : vpiAcceptOnOp;
  return node.synchronous ? vpiSyncRejectOnOp : vpiRejectOnOp;
}

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

VpiObject* WithStrength(VpiObject* sequence, bool strong) {
  if (sequence != nullptr && sequence->type == vpiOperation) {
    sequence->op_strong = strong;
  }
  return sequence;
}

VpiObject* UnclockedPropertyExpr(const PropertyExprNode* node,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing) {
  using Kind = PropertyExprNode::Kind;
  switch (node->kind) {
    case Kind::kBoolean:
      return VpiPropertyOperandObject(*node->boolean, with);
    case Kind::kSequence:
      return WithStrength(SequenceOperand(node->sequence, with, flowing),
                          node->strong);
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
  VpiObject* property = UnclockedPropertyExpr(
      node, with, node->clock.empty() ? flowing : &node->clock);
  if (property == nullptr || node->clock.empty()) return property;
  VpiObject* clocked = with.build.alloc();
  clocked->type = vpiClockedProp;
  clocked->clocking_event = VpiEventCondition(node->clock, with);
  clocked->children.push_back(property);
  return clocked;
}

void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx) {
  const SourceManager& sources = ctx.GetDiag().Sources();
  if (range.start.IsValid()) {
    if (sources.IsProtected(range.start)) obj->is_protected = true;
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

void VpiRecordWrittenLocation(VpiObject* obj, SourceLoc loc, SimContext& ctx) {
  if (!loc.IsValid()) return;
  const SourceManager& sources = ctx.GetDiag().Sources();
  if (sources.IsProtected(loc)) obj->is_protected = true;
  const SourceLoc kWritten = sources.ResolveToOrigin(loc);
  obj->line_no = static_cast<int>(kWritten.line);
  obj->file = std::string(sources.FilePath(kWritten.file_id));
}

VpiObject* VpiMakeItemAssertion(const RtlirAssertion& assertion,
                                VpiObject* scope, SimContext& ctx,
                                const VpiStmtBuild& with) {
  const ModuleItem& item = *assertion.item;
  if (item.body != nullptr && item.body->is_deferred) return nullptr;
  VpiObject* obj = MakeConcurrentAssertion(item, scope, ctx, with.build);
  if (item.body != nullptr) {
    VpiFillAssertionClock(obj, *item.body, with);
    if (assertion.leading_clock != nullptr) {
      obj->clocking_event = VpiEventCondition(*assertion.leading_clock, with);
    }
  }
  if (!item.prop_instance_name.empty() && item.assert_expr != nullptr) {
    VpiMakePropertyInst(
        obj, *item.assert_expr,
        item.body != nullptr ? item.body->assert_disable_iff : nullptr, with);
  } else if (item.body != nullptr) {
    VpiMakePropertySpec(obj, *item.body, with);
  }
  with.statement(item.assert_pass_stmt, obj);
  obj->else_stmt = with.statement(item.assert_fail_stmt, obj);
  return obj;
}

}  // namespace delta
