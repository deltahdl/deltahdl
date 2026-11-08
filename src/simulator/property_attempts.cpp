#include "simulator/property_attempts.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/evaluation.h"
#include "simulator/instance_bindings.h"
#include "simulator/process.h"
#include "simulator/property_attempts_internal.h"
#include "simulator/property_clocks.h"
#include "simulator/property_instance_clocks.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_locals.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

void MarkAborted(NodeState& state, const PropertyExprNode* node) {
  if (state.abort_node == node) state.aborted = true;
  for (NodeState* operand : state.operands) MarkAborted(*operand, node);
  for (NodeState* c : state.consequents) MarkAborted(*c, node);
  for (NodeState* c : state.seconds) MarkAborted(*c, node);
}

void WatchAsynchronousAbort(const PropertyExprNode* node,
                            PropertyTreeState& state, SimContext& ctx,
                            Arena& arena) {
  std::unordered_set<std::string> names;
  CollectExprReads(node->boolean, names);
  for (const std::string& name : names) {
    Variable* var = ctx.FindVariable(name);
    if (var == nullptr) continue;
    var->AddWatcher([node, &state, &ctx, &arena]() {
      if (EvalExpr(node->boolean, ctx, arena).IsTruthy()) {
        for (NodeState* attempt : state.attempts) MarkAborted(*attempt, node);
      }
      return false;
    });
  }
}

void NumberOperandClocks(LinearSequence& body, PropertyClocks& clocks,
                         int inherited) {
  int own_clock = body.declared_clock.empty()
                      ? inherited
                      : ClockIndexOf(clocks, body.declared_clock);
  body.clock_out_index =
      body.clock_out.empty() ? inherited : ClockIndexOf(clocks, body.clock_out);
  if (body.operand_clocks.empty() && own_clock == 0) return;
  body.operand_clock_index.assign(body.operands.size(), own_clock);
  for (size_t j = 0; j < body.operands.size(); ++j) {
    const std::vector<EventExpr>& own = OperandClock(body, j);
    if (!own.empty()) body.operand_clock_index[j] = ClockIndexOf(clocks, own);
  }
}

int ClockOfNode(const PropertyExprNode* node, PropertyTreeState& state,
                int inherited) {
  if (!node->clock.empty()) return ClockIndexOf(state.clocks, node->clock);
  if (node->sequence == nullptr) return inherited;
  for (const FlatSequence& flat : state.sequences) {
    if (flat.node == node && !flat.body.operand_clock_index.empty()) {
      return flat.body.operand_clock_index[0];
    }
  }
  return inherited;
}

struct Collection {
  PropertyTreeState& state;
  SimContext& ctx;
  Arena& arena;
  const ActualsByFormal& actuals;
  ActualsByFormal locals;
};

void AddLocalCopies(const PropertyExprNode* node, Collection& in) {
  for (const LocalCopy& copy : in.state.local_copies) {
    if (copy.node == node) in.locals[copy.name] = copy.reference;
  }
}

ActualsByFormal SubstitutedActuals(const Collection& in) {
  ActualsByFormal all = in.actuals;
  for (const auto& [name, literal] : in.locals) all[name] = literal;
  return all;
}

bool CollectSequences(const PropertyExprNode* node, Collection& in,
                      int inherited) {
  PropertyTreeState& state = in.state;
  int own =
      node->clock.empty() ? inherited : ClockIndexOf(state.clocks, node->clock);
  ActualsByFormal outer_locals = in.locals;
  AddLocalCopies(node, in);
  if (node->boolean != nullptr) {
    CollectPastDirectedSites(node->boolean, state.past_sites);
  }
  if (node->kind == PropertyExprNode::Kind::kAbort && !node->synchronous) {
    WatchAsynchronousAbort(node, state, in.ctx, in.arena);
  }
  if (node->sequence != nullptr) {
    FlatSequence flat{node, LinearSequence{}};
    if (!FlattenLinearSequence(node->sequence, in.ctx, in.arena, flat.body)) {
      return false;
    }
    if (!in.actuals.empty() || !in.locals.empty()) {
      flat.body = SubstituteLinearSequence(flat.body, SubstitutedActuals(in),
                                           in.ctx, in.arena);
    }
    NumberOperandClocks(flat.body, state.clocks, own);
    ForEachLinearSequenceExpr(flat.body, [&state](const Expr* e) {
      CollectPastDirectedSites(e, state.past_sites);
    });
    state.sequences.push_back(std::move(flat));
  }
  for (const PropertyExprNode* operand : node->operands) {
    if (!CollectSequences(operand, in, own)) return false;
  }
  in.locals = std::move(outer_locals);
  return true;
}

PropertyExprNode* SubstituteTree(const PropertyExprNode* node,
                                 const ActualsByFormal& actuals, Arena& arena);

const PropertyExprNode* ActualProperty(const Expr* e,
                                       const ActualsByFormal& actuals) {
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return nullptr;
  auto it = actuals.find(e->text);
  if (it == actuals.end() || it->second == nullptr) return nullptr;
  return ActualTree(it->second);
}

void SubstituteActualProperties(Expr* instance, const ActualsByFormal& actuals,
                                Arena& arena) {
  if (instance == nullptr || instance->kind != ExprKind::kCall ||
      actuals.empty()) {
    return;
  }
  for (Expr* arg : instance->args) {
    if (arg != nullptr && arg->property_actual != nullptr) {
      arg->property_actual =
          SubstituteTree(arg->property_actual, actuals, arena);
    }
  }
}

PropertyExprNode* SubstituteTree(const PropertyExprNode* node,
                                 const ActualsByFormal& actuals, Arena& arena) {
  if (node->kind == PropertyExprNode::Kind::kBoolean) {
    if (const PropertyExprNode* actual =
            ActualProperty(node->boolean, actuals)) {
      return SubstituteTree(actual, ActualsByFormal{}, arena);
    }
  }
  auto* copy = arena.Create<PropertyExprNode>(*node);
  copy->boolean = SubstituteFormals(node->boolean, actuals, arena);
  SubstituteActualProperties(copy->boolean, actuals, arena);
  copy->range_min = SubstituteFormals(node->range_min, actuals, arena);
  copy->range_max = SubstituteFormals(node->range_max, actuals, arena);
  for (std::vector<Expr*>& values : copy->case_values) {
    for (Expr*& value : values) {
      value = SubstituteFormals(value, actuals, arena);
    }
  }
  copy->operands.clear();
  for (const PropertyExprNode* operand : node->operands) {
    copy->operands.push_back(SubstituteTree(operand, actuals, arena));
  }
  return copy;
}

const LinearSequence& BodyOf(const PropertyTreeState& state,
                             const PropertyExprNode* node) {
  for (const FlatSequence& flat : state.sequences) {
    if (flat.node == node) return flat.body;
  }
  return state.sequences.front().body;
}

NodeState* NewNodeState(const PropertyExprNode* node, PropertyTreeState& tree,
                        int inherited, Arena& arena) {
  auto* state = arena.Create<NodeState>();
  if (node->kind == PropertyExprNode::Kind::kAbort) state->abort_node = node;
  state->strong =
      node->strong || (!node->strength_written && tree.plain_sequences_strong);
  state->clock = ClockOfNode(node, tree, inherited);
  for (const PropertyExprNode* operand : node->operands) {
    state->operands.push_back(NewNodeState(operand, tree, state->clock, arena));
  }
  return state;
}

struct StepContext {
  PropertyTreeState& tree;
  SimContext& ctx;
  Arena& arena;
  uint32_t ticked = ~0u;
};

bool Ticked(const StepContext& sc, int clock) {
  return clock >= 32 || ((sc.ticked >> clock) & 1u) != 0;
}

Tri Step(const PropertyExprNode* node, NodeState& state, StepContext& sc,
         bool begin);

std::pair<Expr*, Variable*> NewExpansionLocal(SeqLocalDecl decl,
                                              NodeState& state,
                                              StepContext& sc) {
  std::string name =
      std::string(decl.name) + "@c" + std::to_string(sc.tree.locals_made++);
  decl.name = {sc.arena.AllocString(name.data(), name.size()), name.size()};
  sc.ctx.PushScope();
  Variable* var = StandUpUnassignedLocal(decl, sc.ctx, sc.arena);
  sc.ctx.PopScope();
  state.locals.emplace_back(decl.name, var);
  auto* reference = sc.arena.Create<Expr>();
  reference->kind = ExprKind::kIdentifier;
  reference->text = decl.name;
  return {reference, var};
}

void CaptureLocalFormals(const ModuleItem* decl, ActualsByFormal& actuals,
                         NodeState& state, StepContext& sc) {
  for (size_t i = 0;
       i < decl->prop_formals.size() && i < decl->prop_formal_is_local.size();
       ++i) {
    if (!decl->prop_formal_is_local[i]) continue;
    auto it = actuals.find(decl->prop_formals[i]);
    if (it == actuals.end() || it->second == nullptr ||
        it->second->property_actual != nullptr) {
      continue;
    }
    auto [reference, var] =
        NewExpansionLocal(LocalFormalDecl(*decl, i), state, sc);
    AssignWholeLocal(*var, EvalExpr(it->second, sc.ctx, sc.arena), sc.arena);
    it->second = reference;
  }
}

void SubstituteNodeLocals(PropertyExprNode* node, const ActualsByFormal& locals,
                          Arena& arena) {
  node->boolean = SubstituteFormals(node->boolean, locals, arena);
  SubstituteActualProperties(node->boolean, locals, arena);
  node->range_min = SubstituteFormals(node->range_min, locals, arena);
  node->range_max = SubstituteFormals(node->range_max, locals, arena);
  for (std::vector<Expr*>& values : node->case_values) {
    for (Expr*& value : values) value = SubstituteFormals(value, locals, arena);
  }
}

ActualsByFormal NewLocalCopies(const PropertyExprNode* node,
                               const std::vector<SeqLocalDecl>& locals,
                               NodeState& state, StepContext& sc) {
  ActualsByFormal copies;
  for (const SeqLocalDecl& local : locals) {
    auto [reference, var] = NewExpansionLocal(local, state, sc);
    const Expr* init = SubstituteFormals(local.init, copies, sc.arena);
    sc.tree.local_copies.push_back({node, local.name, reference, init, var});
    copies[local.name] = reference;
  }
  return copies;
}

bool NamesAClock(const PropertyExprNode* node) {
  if (!node->clock.empty()) return true;
  if (node->sequence == nullptr) return false;
  const SeqLinearBody& body = node->sequence->seq_linear;
  return !body.clocks.empty() && !body.clocks.front().empty();
}

void PlaceLocalCopies(PropertyExprNode* node,
                      const std::vector<SeqLocalDecl>& locals,
                      const ActualsByFormal* in_force, NodeState& state,
                      StepContext& sc) {
  ActualsByFormal own;
  if (in_force == nullptr || NamesAClock(node)) {
    own = NewLocalCopies(node, locals, state, sc);
    in_force = &own;
  }
  SubstituteNodeLocals(node, *in_force, sc.arena);
  for (PropertyExprNode* operand : node->operands) {
    PlaceLocalCopies(operand, locals, in_force, state, sc);
  }
}

void InitializeLocalCopies(const PropertyExprNode* node, StepContext& sc) {
  std::vector<LocalCopy>& copies = sc.tree.local_copies;
  std::vector<LocalCopy> waiting;
  waiting.reserve(copies.size());
  for (LocalCopy& copy : copies) {
    if (copy.node != node) {
      waiting.push_back(copy);
      continue;
    }
    if (copy.init == nullptr) continue;
    AssignWholeLocal(*copy.var, EvalExpr(copy.init, sc.ctx, sc.arena),
                     sc.arena);
  }
  copies = std::move(waiting);
}

bool ExpandInstance(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc) {
  const ModuleItem* decl = InstantiatedProperty(node->boolean, sc.ctx);
  if (decl == nullptr) return false;
  auto actuals = BindInstanceActuals(decl, node->boolean, sc.arena);
  CaptureLocalFormals(decl, actuals, state, sc);
  PropertyExprNode* body =
      SubstituteTree(decl->prop_body_tree, actuals, sc.arena);
  if (body->clock.empty()) {
    body->clock = SubstituteClock(decl->prop_clock, actuals, sc.arena);
  }
  if (!decl->prop_locals.empty()) {
    PlaceLocalCopies(body, decl->prop_locals, nullptr, state, sc);
  }
  Collection collection{sc.tree, sc.ctx, sc.arena, actuals, {}};
  if (!CollectSequences(body, collection, state.clock)) return false;
  InstallClockWatchers(sc.tree.clocks, sc.ctx, sc.arena);
  sc.ticked = ClocksTicked(
      sc.tree.clocks, sc.ctx.AssertionSamples().StepTime(sc.ctx.CurrentTime()));
  sc.ctx.AssertionSamples().SetClockTicks(sc.ticked);
  state.expansion = body;
  state.operands.push_back(NewNodeState(body, sc.tree, state.clock, sc.arena));
  return true;
}

Tri StepBoolean(const PropertyExprNode* node, NodeState& state, StepContext& sc,
                bool begin) {
  if (begin) ExpandInstance(node, state, sc);
  if (state.expansion != nullptr) {
    sc.ctx.PushScope();
    for (const auto& [name, var] : state.locals) {
      sc.ctx.BindLocalVariable(name, var);
    }
    Tri verdict = Step(state.expansion, *state.operands[0], sc, begin);
    sc.ctx.PopScope();
    return verdict;
  }
  const bool kHeld = EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy();
  sc.ctx.AssertionSamples().NoteOperand(node->boolean, kHeld);
  return FromBool(kHeld);
}

Tri StepSequence(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  const LinearSequence& body = BodyOf(sc.tree, node);
  if (begin) state.attempt = NewSequenceAttempt(body, sc.arena);
  SequenceStep step =
      StepSequenceAttempt(body, *state.attempt, begin, sc.ctx, sc.arena);
  state.matches_again = step == SequenceStep::kMatched;
  return FromStep(step);
}

Tri StepJunction(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  std::vector<Tri> verdicts;
  verdicts.reserve(node->operands.size());
  for (size_t i = 0; i < node->operands.size(); ++i) {
    verdicts.push_back(Step(node->operands[i], *state.operands[i], sc, begin));
  }
  return Junction(node->kind == PropertyExprNode::Kind::kOr, verdicts);
}

Tri StepIfElse(const PropertyExprNode* node, NodeState& state, StepContext& sc,
               bool begin) {
  if (begin) {
    state.condition = EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy();
  }
  Tri then_branch = Step(node->operands[0], *state.operands[0], sc, begin);
  Tri else_branch = node->operands.size() > 1
                        ? Step(node->operands[1], *state.operands[1], sc, begin)
                        : Tri::kTrue;
  return state.condition ? then_branch : else_branch;
}

size_t SelectCaseItem(const PropertyExprNode* node, StepContext& sc) {
  CaseLength length;
  IncludeInCaseLength(node->boolean, sc.ctx, length);
  for (const std::vector<Expr*>& values : node->case_values) {
    for (const Expr* value : values) {
      IncludeInCaseLength(value, sc.ctx, length);
    }
  }
  Logic4Vec sel = CaseOperandValue(node->boolean, length, sc.ctx, sc.arena);
  size_t selected = node->operands.size();
  for (size_t i = 0; i < node->case_values.size(); ++i) {
    if (node->case_values[i].empty()) {
      selected = i;
      continue;
    }
    for (const Expr* value : node->case_values[i]) {
      if (CaseExactMatch(sel,
                         CaseOperandValue(value, length, sc.ctx, sc.arena))) {
        return i;
      }
    }
  }
  return selected;
}

Tri StepCase(const PropertyExprNode* node, NodeState& state, StepContext& sc,
             bool begin) {
  if (begin) state.selected = SelectCaseItem(node, sc);
  if (state.selected == node->operands.size()) return Tri::kTrue;
  return Step(node->operands[state.selected], *state.operands[state.selected],
              sc, begin);
}

bool StepAntecedent(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool begin) {
  if (state.antecedent_done) return false;
  const LinearSequence& body = BodyOf(sc.tree, node);
  if (begin) state.attempt = NewSequenceAttempt(body, sc.arena);
  SequenceStep step =
      StepSequenceAttempt(body, *state.attempt, begin, sc.ctx, sc.arena);
  if (step == SequenceStep::kFailed || step == SequenceStep::kMatchedLast ||
      (body.first_match && Matched(step))) {
    state.antecedent_done = true;
  }
  if (!Matched(step)) return false;
  if (!node->strong) return true;
  state.spawn_next = true;
  return false;
}

int ConsequentClock(const PropertyExprNode* node, const NodeState& state,
                    StepContext& sc) {
  int own = ClockOfNode(node->operands[0], sc.tree, -1);
  if (own >= 0) return own;
  const LinearSequence& antecedent = BodyOf(sc.tree, node);
  if (!antecedent.operand_clock_index.empty()) {
    return antecedent.clock_out_index;
  }
  return state.clock;
}

Tri StepImplication(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool begin) {
  const PropertyExprNode* consequent = node->operands[0];
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size() + 1);
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Step(consequent, *c, sc, false));
  }
  int clock = ConsequentClock(node, state, sc);
  bool spawn_now = state.spawn_next && Ticked(sc, clock);
  if (spawn_now) state.spawn_next = false;
  if (StepAntecedent(node, state, sc, begin)) {
    if (Ticked(sc, clock)) {
      spawn_now = true;
    } else {
      state.spawn_next = true;
    }
  }
  if (spawn_now) {
    NodeState* c = NewNodeState(consequent, sc.tree, clock, sc.arena);
    state.consequents.push_back(c);
    verdicts.push_back(Step(consequent, *c, sc, true));
  }
  Tri all = Junction(false, verdicts);
  if (all == Tri::kFalse) return Tri::kFalse;
  if (state.antecedent_done && !state.spawn_next && all == Tri::kTrue) {
    return Tri::kTrue;
  }
  return Tri::kPending;
}

Tri StepNexttime(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  if (begin) {
    state.wait = node->boolean != nullptr
                     ? EvalExpr(node->boolean, sc.ctx, sc.arena).ToUint64()
                     : 1;
  } else if (!state.begun) {
    --state.wait;
  }
  if (!state.begun && state.wait > 0) return Tri::kPending;
  bool first = !state.begun;
  state.begun = true;
  return Step(node->operands[0], *state.operands[0], sc, first);
}

uint64_t EvalCount(const Expr* e, StepContext& sc, uint64_t absent) {
  if (e == nullptr) return absent;
  return EvalExpr(e, sc.ctx, sc.arena).ToUint64();
}

Tri StepAlways(const PropertyExprNode* node, NodeState& state, StepContext& sc,
               bool begin) {
  const PropertyExprNode* operand = node->operands[0];
  if (begin) {
    state.wait = EvalCount(node->range_min, sc, 0);
    state.remaining = node->range_unbounded
                          ? UINT64_MAX
                          : EvalCount(node->range_max, sc, 0) - state.wait + 1;
  } else if (state.wait > 0) {
    --state.wait;
  }
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size() + 1);
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Step(operand, *c, sc, false));
  }
  if (state.wait == 0 && state.remaining > 0) {
    NodeState* c = NewNodeState(operand, sc.tree, state.clock, sc.arena);
    state.consequents.push_back(c);
    verdicts.push_back(Step(operand, *c, sc, true));
    if (!node->range_unbounded) --state.remaining;
  }
  bool eventually = node->kind == PropertyExprNode::Kind::kEventually;
  Tri joined = Junction(eventually, verdicts);
  Tri decisive = eventually ? Tri::kTrue : Tri::kFalse;
  if (joined == decisive) return decisive;
  return state.remaining == 0 ? joined : Tri::kPending;
}

Tri StepUntil(const PropertyExprNode* node, NodeState& state, StepContext& sc) {
  std::vector<Tri> firsts;
  std::vector<Tri> seconds;
  firsts.reserve(state.consequents.size() + 1);
  seconds.reserve(state.seconds.size() + 1);
  for (size_t i = 0; i < state.consequents.size(); ++i) {
    firsts.push_back(Step(node->operands[0], *state.consequents[i], sc, false));
    seconds.push_back(Step(node->operands[1], *state.seconds[i], sc, false));
  }
  NodeState* first =
      NewNodeState(node->operands[0], sc.tree, state.clock, sc.arena);
  NodeState* second =
      NewNodeState(node->operands[1], sc.tree, state.clock, sc.arena);
  state.consequents.push_back(first);
  state.seconds.push_back(second);
  firsts.push_back(Step(node->operands[0], *first, sc, true));
  seconds.push_back(Step(node->operands[1], *second, sc, true));
  return DecideUntil(node, state, firsts, seconds);
}

Tri StepAbort(const PropertyExprNode* node, NodeState& state, StepContext& sc,
              bool begin) {
  bool fired =
      state.aborted || EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy();
  if (fired) return node->accept ? Tri::kTrue : Tri::kFalse;
  return Step(node->operands[0], *state.operands[0], sc, begin);
}

bool AdvancesOffItsClock(const PropertyExprNode* node, const NodeState& state) {
  switch (node->kind) {
    case PropertyExprNode::Kind::kSequence:
    case PropertyExprNode::Kind::kImplication:
    case PropertyExprNode::Kind::kNot:
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd:
    case PropertyExprNode::Kind::kIfElse:
    case PropertyExprNode::Kind::kCase:
      return true;
    case PropertyExprNode::Kind::kBoolean:
      return state.expansion != nullptr;
    case PropertyExprNode::Kind::kNexttime:
      return state.begun;
    case PropertyExprNode::Kind::kImplies:
    case PropertyExprNode::Kind::kIff:
    case PropertyExprNode::Kind::kAlways:
    case PropertyExprNode::Kind::kUntil:
    case PropertyExprNode::Kind::kEventually:
    case PropertyExprNode::Kind::kAbort:
      return false;
  }
  return false;
}

bool AdvancesAtTick(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool& begin) {
  bool own_tick = Ticked(sc, state.clock);
  if (begin && !own_tick) {
    state.awaiting = true;
    return false;
  }
  if (state.awaiting) {
    if (!own_tick) return false;
    state.awaiting = false;
    begin = true;
  }
  if (!own_tick && !AdvancesOffItsClock(node, state)) return false;
  if (begin && !sc.tree.local_copies.empty()) InitializeLocalCopies(node, sc);
  return true;
}

Tri Step(const PropertyExprNode* node, NodeState& state, StepContext& sc,
         bool begin) {
  if (state.verdict != Tri::kPending) return state.verdict;
  if (!AdvancesAtTick(node, state, sc, begin)) return state.verdict;
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      state.verdict = StepBoolean(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kSequence:
      state.verdict = StepSequence(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kNot:
      state.verdict =
          Not(Step(node->operands[0], *state.operands[0], sc, begin));
      break;
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd:
      state.verdict = StepJunction(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kIfElse:
      state.verdict = StepIfElse(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kImplication:
      state.verdict = StepImplication(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kNexttime:
      state.verdict = StepNexttime(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kAlways:
    case PropertyExprNode::Kind::kEventually:
      state.verdict = StepAlways(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kUntil:
      state.verdict = StepUntil(node, state, sc);
      break;
    case PropertyExprNode::Kind::kAbort:
      state.verdict = StepAbort(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kCase:
      state.verdict = StepCase(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kImplies:
    case PropertyExprNode::Kind::kIff: {
      Tri first = Step(node->operands[0], *state.operands[0], sc, begin);
      Tri second = Step(node->operands[1], *state.operands[1], sc, begin);
      state.verdict = node->kind == PropertyExprNode::Kind::kImplies
                          ? Implies(first, second)
                          : Iff(first, second);
      break;
    }
  }
  return state.verdict;
}

}  // namespace

PropertyTreeState* CreatePropertyTreeState(
    const PropertyExprNode* root, const std::vector<EventExpr>& leading_clock,
    bool every_match, SimContext& ctx, Arena& arena) {
  auto* state = arena.Create<PropertyTreeState>();
  state->every_match = every_match;
  const ActualsByFormal kActuals =
      CheckerTreeActuals(ctx.ActiveInstancePrefix(), ctx);
  if (!kActuals.empty()) root = SubstituteTree(root, kActuals, arena);
  state->root = root;
  state->clocks.clocks.push_back(
      SubstituteClock(leading_clock, kActuals, arena));
  Collection collection{*state, ctx, arena, kActuals, {}};
  if (!CollectSequences(root, collection, 0)) return nullptr;
  RegisterInstanceBodyClocks(root, state->clocks, ctx, arena);
  InstallClockWatchers(state->clocks, ctx, arena);
  Process* proc = ctx.CurrentProcess();
  if (proc != nullptr && WokenByAnotherClock(state->clocks, proc->woken_by)) {
    state->clocks.installed_at = PropertyClocks::kNever;
  }
  return state;
}

static bool MatchesAgain(const PropertyTreeState& state,
                         const NodeState& root) {
  return state.every_match &&
         state.root->kind == PropertyExprNode::Kind::kSequence &&
         root.verdict == Tri::kTrue && root.matches_again;
}

static void StepAttempts(StepContext& sc, size_t beginning, size_t advanced,
                         PropertyTick& tick) {
  PropertyTreeState& state = sc.tree;
  auto& samples = sc.ctx.AssertionSamples();
  std::vector<NodeState*> kept;
  for (size_t i = 0; i < state.attempts.size(); ++i) {
    if (i < advanced) {
      kept.push_back(state.attempts[i]);
      continue;
    }
    bool first = i + beginning >= state.attempts.size();
    samples.SetInstanceBindings(state.attempts[i]->bindings);
    samples.NoteAttemptStepped(state.attempts[i]->started);
    Tri verdict = Step(state.root, *state.attempts[i], sc, first);
    samples.SetInstanceBindings(nullptr);
    if (verdict == Tri::kPending) {
      kept.push_back(state.attempts[i]);
      continue;
    }
    tick.verdicts.push_back(VerdictOf(state.root, *state.attempts[i]));
    if (MatchesAgain(state, *state.attempts[i])) {
      state.attempts[i]->verdict = Tri::kPending;
      kept.push_back(state.attempts[i]);
    }
  }
  state.attempts = std::move(kept);
}

PropertyTick AdvancePropertyTree(PropertyTreeState& state, bool disabled,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena) {
  PropertyTick tick;
  SimTime now = ctx.AssertionSamples().StepTime(ctx.CurrentTime());
  if (state.clocks.multiclock && state.advanced_at == now) return tick;
  bool again = state.advanced_at == now;
  state.advanced_at = now;
  uint32_t ticked = ClocksTicked(state.clocks, now);
  ForgetTicksBefore(state.clocks, now);
  if (ticked == 0) return tick;
  size_t beginning = (ticked & 1u) != 0 ? instances.size() : 0;
  tick.attempted = static_cast<uint32_t>(beginning);
  auto& samples = ctx.AssertionSamples();
  samples.SetClockTicks(ticked);
  for (const Expr* site : state.past_sites) EvalExpr(site, ctx, arena);
  if (disabled) {
    for (NodeState* attempt : state.attempts) {
      tick.disabled.push_back(attempt->started);
    }
    tick.disabled.insert(tick.disabled.end(), beginning, now.ticks);
    state.attempts.clear();
    samples.SetClockTicks(~0u);
    return tick;
  }
  size_t advanced = again ? state.attempts.size() : 0;
  for (size_t i = 0; i < beginning; ++i) {
    NodeState* attempt = NewNodeState(state.root, state, 0, arena);
    attempt->bindings = instances[i];
    attempt->started = now.ticks;
    state.attempts.push_back(attempt);
  }
  StepContext sc{state, ctx, arena, ticked};
  StepAttempts(sc, beginning, advanced, tick);
  samples.SetClockTicks(~0u);
  return tick;
}

}  // namespace delta
