#include "simulator/property_attempts.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/expr_walk.h"
#include "simulator/instance_bindings.h"
#include "simulator/property_attempts_internal.h"
#include "simulator/property_clocks.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §16.13.7: one copy of a local variable of a named property for one
// semantic leading clock of an instance's attempt: the node of the
// expansion it is for, whose subtree reads `literal` in the local's place,
// and the initialization assignment performed, into the literal, at the
// first tick of that node's clock at or after the attempt begins.
struct LocalCopy {
  const PropertyExprNode* node;
  std::string_view name;
  Expr* literal;
  const Expr* init;
  TokenKind type_kw;
};

struct PropertyTreeState {
  const PropertyExprNode* root = nullptr;
  std::vector<FlatSequence> sequences;
  std::vector<const Expr*> past_sites;
  std::vector<NodeState*> attempts;
  std::vector<LocalCopy> local_copies;
  // §16.13: the clocks the sequences are evaluated on, the leading clock
  // first, and the time step the tree last advanced at.
  PropertyClocks clocks;
  SimTime advanced_at{PropertyClocks::kNever};
};

namespace {

// §16.9.3: the sampled value functions the tree's booleans and sequences
// hold, sampled at every tick as a procedure's are.
bool IsPastDirectedCall(const Expr* e) {
  if (e->kind != ExprKind::kSystemCall) return false;
  return e->callee == "$past" || e->callee == "$rose" || e->callee == "$fell" ||
         e->callee == "$stable" || e->callee == "$changed";
}

void CollectPastDirectedSites(const Expr* e, std::vector<const Expr*>& sites) {
  ForEachSubExpr(e, [&sites](const Expr* sub) {
    if (IsPastDirectedCall(sub)) sites.push_back(sub);
  });
}

// §16.12.14: marks the states of the abort `node` in the attempt under
// `state`, in flight at the time step the condition became true at.
void MarkAborted(NodeState& state, const PropertyExprNode* node) {
  if (state.abort_node == node) state.aborted = true;
  for (NodeState* operand : state.operands) MarkAborted(*operand, node);
  for (NodeState* c : state.consequents) MarkAborted(*c, node);
  for (NodeState* c : state.seconds) MarkAborted(*c, node);
}

// §16.12.14: an asynchronous abort's condition is checked at the
// granularity of the simulation time step, so each variable it reads is
// watched, and a change that makes it true marks the attempts in flight.
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

// §16.13.1: each operand of the flattened sequence given the number of its
// clock among the property's, where the sequence names any or is evaluated
// on a clock other than the leading, an operand naming none on the clock
// flowing to the sequence, `inherited`.
void NumberOperandClocks(LinearSequence& body, PropertyClocks& clocks,
                         int inherited) {
  // §16.13.3: a named sequence declared with a clock is evaluated on it,
  // which flows no further than the sequence.
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

// §16.13.2 and §16.13.3: the number of the clock the node is evaluated on,
// its own where it names one, numbered where new, and otherwise the one
// flowing to it from its parent, `inherited`; a sequence, an implication's
// antecedent included, names its first operand's.
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

// What a collection of the tree's sequences reads and writes: the tree's
// state, the context and arena the sequences are flattened in, and the
// actuals of the instance the tree is the expansion of.
struct Collection {
  PropertyTreeState& state;
  SimContext& ctx;
  Arena& arena;
  const ActualsByFormal& actuals;
  // §16.13.7: the copies of the property's locals in force under the node,
  // by the local's name, the sequences under it substituted with them.
  ActualsByFormal locals;
};

// §16.13.7: the copies of the locals made for `node`, where any were,
// added to the copies in force above it.
void AddLocalCopies(const PropertyExprNode* node, Collection& in) {
  for (const LocalCopy& copy : in.state.local_copies) {
    if (copy.node == node) in.locals[copy.name] = copy.literal;
  }
}

// The actuals a sequence under the node is substituted with: the
// instance's and the local copies in force.
ActualsByFormal SubstitutedActuals(const Collection& in) {
  ActualsByFormal all = in.actuals;
  for (const auto& [name, literal] : in.locals) all[name] = literal;
  return all;
}

// The sequences of the tree flattened, each node's once, with the actuals
// substituted where the collection holds any, each operand numbered by its
// clock, `inherited` the clock flowing to the node; answers false where a
// sequence is not readable.
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

// §16.12.18: the tree the actual of a formal carries where `e` references
// the formal and the actual is a sequence_expr or a property_expr; nullptr
// for any other expression.
const PropertyExprNode* ActualProperty(const Expr* e,
                                       const ActualsByFormal& actuals) {
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return nullptr;
  auto it = actuals.find(e->text);
  if (it == actuals.end() || it->second == nullptr) return nullptr;
  return it->second->property_actual;
}

// §16.12.18: the sequences and properties passed as actuals to an instance
// in the body read the formals as the body's expressions do, so the tree
// each such argument carries is substituted too; the argument is the copy
// the expression substitution made.
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

// §F.4.1: a copy of the tree under `node` with the actuals substituted for
// the formals in every expression it holds; a sequence is shared with the
// original and substituted where it is flattened. §16.12.18: a boolean
// operand that references a formal whose actual is a sequence_expr or a
// property_expr stands for the actual, copied so that its nodes are the
// expansion's own.
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

// The state of one attempt of the tree under `node`, its operators' operands
// stood up with it and its sequences' attempts to be begun at the first
// tick.
NodeState* NewNodeState(const PropertyExprNode* node, PropertyTreeState& tree,
                        int inherited, Arena& arena) {
  auto* state = arena.Create<NodeState>();
  if (node->kind == PropertyExprNode::Kind::kAbort) state->abort_node = node;
  state->clock = ClockOfNode(node, tree, inherited);
  for (const PropertyExprNode* operand : node->operands) {
    state->operands.push_back(NewNodeState(operand, tree, state->clock, arena));
  }
  return state;
}

// What one tick's steps read: the tree with its flattened sequences, the
// context and the arena.
struct StepContext {
  PropertyTreeState& tree;
  SimContext& ctx;
  Arena& arena;
  // §16.13: the clocks that ticked at the time step, a bit per clock, on
  // which each node advances where its own did.
  uint32_t ticked = ~0u;
};

bool Ticked(const StepContext& sc, int clock) {
  return clock >= 32 || ((sc.ticked >> clock) & 1u) != 0;
}

// One tick of one attempt's node, `begin` where the tick is the one the
// attempt begins at, answering the node's verdict so far.
Tri Step(const PropertyExprNode* node, NodeState& state, StepContext& sc,
         bool begin);

// §16.12.19 by way of §16.8.2: a local variable formal argument of a named
// property, whose direction is input alone, is a local variable of the
// instance, a new copy of it initialized from the actual when the attempt
// begins, so the actual's value at that tick, sampled as the property reads
// it and cast as §16.8.1 has it, stands in the formal's place for the
// attempt where the actual is an expression.
void CaptureLocalFormals(const ModuleItem* decl, ActualsByFormal& actuals,
                         StepContext& sc) {
  for (size_t i = 0;
       i < decl->prop_formals.size() && i < decl->prop_formal_is_local.size();
       ++i) {
    if (!decl->prop_formal_is_local[i]) continue;
    auto it = actuals.find(decl->prop_formals[i]);
    if (it == actuals.end() || it->second == nullptr ||
        it->second->property_actual != nullptr) {
      continue;
    }
    it->second =
        LiteralOfValue(EvalExpr(it->second, sc.ctx, sc.arena), sc.arena);
  }
}

// §16.13.7: the expressions of one node of an expansion with the copies of
// the locals in force substituted for the locals, in place, the node being
// the expansion's own; a sequence is substituted where it is flattened.
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

// §16.13.7: a copy of each of the property's locals for `node`, one of the
// expansion's nodes that names a clock or its root, the initialization of
// each reading the copies of the locals declared before it; the copies by
// the locals' names.
ActualsByFormal NewLocalCopies(const PropertyExprNode* node,
                               const std::vector<SeqLocalDecl>& locals,
                               PropertyTreeState& tree, Arena& arena) {
  ActualsByFormal copies;
  for (const SeqLocalDecl& local : locals) {
    Logic4Vec unassigned = MakeLogic4Vec(arena, LocalWidth(local.type_kw));
    FillWithX(unassigned);
    Expr* literal = LiteralOfValue(unassigned, arena);
    const Expr* init = SubstituteFormals(local.init, copies, arena);
    tree.local_copies.push_back(
        {node, local.name, literal, init, local.type_kw});
    copies[local.name] = literal;
  }
  return copies;
}

// §16.13.2: whether the node names a clock of its own, `@(posedge clk1)`
// before it or before the first operand of the sequence it holds.
bool NamesAClock(const PropertyExprNode* node) {
  if (!node->clock.empty()) return true;
  if (node->sequence == nullptr) return false;
  const SeqLinearBody& body = node->sequence->seq_linear;
  return !body.clocks.empty() && !body.clocks.front().empty();
}

// §16.13.7: a separate copy of each local of the property for each semantic
// leading clock of the expansion, the clock a node names being one and the
// clock flowing into the root another, each subtree reading the copy of the
// nearest clock above it, and a copy's initialization performed at the
// first tick of its clock at or after the attempt begins, which is where
// its node begins.
void PlaceLocalCopies(PropertyExprNode* node,
                      const std::vector<SeqLocalDecl>& locals,
                      const ActualsByFormal* in_force, PropertyTreeState& tree,
                      Arena& arena) {
  ActualsByFormal own;
  if (in_force == nullptr || NamesAClock(node)) {
    own = NewLocalCopies(node, locals, tree, arena);
    in_force = &own;
  }
  SubstituteNodeLocals(node, *in_force, arena);
  for (PropertyExprNode* operand : node->operands) {
    PlaceLocalCopies(operand, locals, in_force, tree, arena);
  }
}

// §16.13.7: the initialization assignments of the copies made for `node`,
// performed as the node begins, at the first tick of its clock at or after
// the attempt began, each in the order the locals are declared, the value
// cast to the local's type; a copy initialized lives on in its literal
// alone.
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
    Logic4Vec value = ResizeToWidth(
        OwnRhsWords(EvalExpr(copy.init, sc.ctx, sc.arena), sc.arena),
        LocalWidth(copy.type_kw), sc.arena);
    *copy.literal = *LiteralOfValue(value, sc.arena);
  }
  copies = std::move(waiting);
}

// §16.12.17: a boolean operand that instantiates a named property is, when
// it begins, expanded to the property's body with the actuals substituted
// for the formals, stood up as the operand's one operand and stepped from
// the tick; an instance in that body, the property's own included, is
// expanded in turn when it begins, after the positive advance in time
// Restriction 3 requires of it. Answers false, the operand a boolean,
// where it instantiates no property or the body is not readable.
bool ExpandInstance(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc) {
  const ModuleItem* decl = InstantiatedProperty(node->boolean, sc.ctx);
  if (decl == nullptr) return false;
  ActualsByFormal actuals = BindInstanceActuals(decl, node->boolean, sc.arena);
  CaptureLocalFormals(decl, actuals, sc);
  PropertyExprNode* body =
      SubstituteTree(decl->prop_body_tree, actuals, sc.arena);
  // §16.13.2: a property declared with a clock is evaluated on it, from its
  // first tick at or after the instance begins, the actuals in the formals'
  // places.
  if (body->clock.empty()) {
    body->clock = SubstituteClock(decl->prop_clock, actuals, sc.arena);
  }
  if (!decl->prop_locals.empty()) {
    PlaceLocalCopies(body, decl->prop_locals, nullptr, sc.tree, sc.arena);
  }
  Collection collection{sc.tree, sc.ctx, sc.arena, actuals, {}};
  if (!CollectSequences(body, collection, state.clock)) return false;
  InstallClockWatchers(sc.tree.clocks, sc.ctx, sc.arena);
  // §16.13.2: a clock the expansion brings has not ticked at this time
  // step, which the step's mask, read before the clock was met, would say
  // of every clock, so the mask is read again for the operands on it to
  // begin at its first tick.
  sc.ticked = ClocksTicked(sc.tree.clocks, sc.ctx.CurrentTime());
  sc.ctx.AssertionSamples().SetClockTicks(sc.ticked);
  state.expansion = body;
  state.operands.push_back(NewNodeState(body, sc.tree, state.clock, sc.arena));
  return true;
}

Tri StepBoolean(const PropertyExprNode* node, NodeState& state, StepContext& sc,
                bool begin) {
  if (begin) ExpandInstance(node, state, sc);
  if (state.expansion != nullptr) {
    return Step(state.expansion, *state.operands[0], sc, begin);
  }
  return FromBool(EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy());
}

Tri StepSequence(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  const LinearSequence& body = BodyOf(sc.tree, node);
  if (begin) state.attempt = NewSequenceAttempt(body, sc.arena);
  return FromStep(
      StepSequenceAttempt(body, *state.attempt, begin, sc.ctx, sc.arena));
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

// §16.12.6: the condition is read at the attempt's tick, and the branch it
// selects is the property; the else absent is true.
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

// §12.5: the case expression and one item's expression are compared with
// the case equality, the narrower extended to the wider's width, signed
// where both are.
bool CaseMatches(Logic4Vec sel, Logic4Vec item, Arena& arena) {
  uint32_t width = sel.width > item.width ? sel.width : item.width;
  bool sign_ext = sel.is_signed && item.is_signed;
  if (sel.width < width) sel = ExtendVec(sel, width, sign_ext, arena);
  if (item.width < width) item = ExtendVec(item, width, sign_ext, arena);
  return EvalCaseEquality(sel, item);
}

// §16.12.16: the linear search over the items in order, the default item
// ignored in it: the first item one of whose expressions matches the case
// expression is selected and the search ends there; where every comparison
// fails the default is selected, and the count of the items where there is
// none.
size_t SelectCaseItem(const PropertyExprNode* node, StepContext& sc) {
  Logic4Vec sel = EvalExpr(node->boolean, sc.ctx, sc.arena);
  size_t selected = node->operands.size();
  for (size_t i = 0; i < node->case_values.size(); ++i) {
    if (node->case_values[i].empty()) {
      selected = i;
      continue;
    }
    for (const Expr* value : node->case_values[i]) {
      if (CaseMatches(sel, EvalExpr(value, sc.ctx, sc.arena), sc.arena)) {
        return i;
      }
    }
  }
  return selected;
}

// §16.12.16: the item is selected at the attempt's tick and its property
// alone is the case's, evaluated from that tick; with no item selected none
// is evaluated and the case holds, vacuously.
Tri StepCase(const PropertyExprNode* node, NodeState& state, StepContext& sc,
             bool begin) {
  if (begin) state.selected = SelectCaseItem(node, sc);
  if (state.selected == node->operands.size()) return Tri::kTrue;
  return Step(node->operands[state.selected], *state.operands[state.selected],
              sc, begin);
}

// §16.12.7: one tick of the antecedent's attempt while it can still match,
// answering whether a consequent is to begin at this tick; a match of the
// nonoverlapped form begins one at the next tick instead.
bool StepAntecedent(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool begin) {
  if (state.antecedent_done) return false;
  const LinearSequence& body = BodyOf(sc.tree, node);
  if (begin) state.attempt = NewSequenceAttempt(body, sc.arena);
  SequenceStep step =
      StepSequenceAttempt(body, *state.attempt, begin, sc.ctx, sc.arena);
  if (step == SequenceStep::kFailed || step == SequenceStep::kMatchedLast) {
    state.antecedent_done = true;
  }
  if (!Matched(step)) return false;
  if (!node->strong) return true;
  state.spawn_next = true;
  return false;
}

// §16.13.2 and §16.13.3: the clock the consequent is evaluated on: its own
// where it names one, else the clock flowing out of the antecedent's end,
// which is the implication's where the antecedent names none outside
// parentheses and instances.
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

// §16.12.7: the antecedent's attempt is stepped until it can match no more,
// and at each tick it matches at a consequent attempt begins, at that tick
// for `|->` and at the next for `|=>`; the implication is false as soon as
// a consequent is, and true once the antecedent can match no more and every
// consequent begun is true, no match of the antecedent making it true.
Tri StepImplication(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool begin) {
  const PropertyExprNode* consequent = node->operands[0];
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size() + 1);
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Step(consequent, *c, sc, false));
  }
  // §16.13.2: a consequent on a clock of its own begins at that clock's
  // nearest tick after the antecedent's end, the coincident one for `|->`
  // and the strictly subsequent one for `|=>`.
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

// §16.12.10: the operand begins at the tick the count of ticks after the
// attempt's has passed, one where none was written, `nexttime [0]` at the
// attempt's own tick; until then the property is not decided.
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

// §16.12.11 and §16.12.13: an operand attempt begins at each tick of the
// range; the always is false as soon as one is false and true once every
// tick of a bounded range has begun one and all are true, and the
// eventually true as soon as one is true and false once every tick of a
// bounded range has begun one and all are false.
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

// One tick of an until: the operands' attempts of the ticks before step on,
// a pair begins at this tick, and the ticks are decided in order.
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

// §16.12.14: the abort condition is read at each tick of the attempt, and
// for the asynchronous forms at each time step between as well, before the
// operand is stepped, so that an abort at the step the operand's evaluation
// ends at takes precedence and the outermost of nested aborts does; the
// condition true makes an accept true and a reject false, and otherwise the
// property is its operand.
Tri StepAbort(const PropertyExprNode* node, NodeState& state, StepContext& sc,
              bool begin) {
  bool fired =
      state.aborted || EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy();
  if (fired) return node->accept ? Tri::kTrue : Tri::kFalse;
  return Step(node->operands[0], *state.operands[0], sc, begin);
}

// §16.13: whether the node advances at a tick of a clock other than its
// own: a sequence, whose operands may be on that clock, and the operators
// whose operands may be and which count no ticks of their own.
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

// §16.13.2: whether the node advances at this tick: an operand on a clock
// of its own begins at that clock's nearest tick, the one it was begun at
// where the clock ticked there, `begin` set where that is this tick, and
// advances at its clock's ticks, and at the others' only where an operand
// of its own may be on them. §16.13.7: the copies of the locals made for
// the node are initialized as it begins.
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

// The verdict of an attempt decided, read off its root's state.
PropertyVerdict VerdictOf(const PropertyExprNode* root,
                          const NodeState& state) {
  PropertyVerdict verdict;
  verdict.holds = state.verdict == Tri::kTrue;
  verdict.vacuous = verdict.holds && !Nonvacuous(root, state);
  verdict.bindings = state.bindings;
  return verdict;
}

}  // namespace

PropertyTreeState* CreatePropertyTreeState(
    const PropertyExprNode* root, const std::vector<EventExpr>& leading_clock,
    SimContext& ctx, Arena& arena) {
  auto* state = arena.Create<PropertyTreeState>();
  state->root = root;
  state->clocks.clocks.push_back(leading_clock);
  const ActualsByFormal kNoActuals;
  Collection collection{*state, ctx, arena, kNoActuals, {}};
  if (!CollectSequences(root, collection, 0)) return nullptr;
  InstallClockWatchers(state->clocks, ctx, arena);
  return state;
}

// The attempts of one tick: the first `advanced`, already stepped at this
// time step, are kept as they stand; the rest step, the last `beginning`
// of them at their first tick, and each that is decided reaches its
// verdict and leaves.
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
    // §16.14.6.1: the attempt reads the values its instance saved.
    samples.SetInstanceBindings(state.attempts[i]->bindings);
    Tri verdict = Step(state.root, *state.attempts[i], sc, first);
    samples.SetInstanceBindings(nullptr);
    if (verdict == Tri::kPending) {
      kept.push_back(state.attempts[i]);
    } else {
      tick.verdicts.push_back(VerdictOf(state.root, *state.attempts[i]));
    }
  }
  state.attempts = std::move(kept);
}

PropertyTick AdvancePropertyTree(PropertyTreeState& state, bool disabled,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena) {
  PropertyTick tick;
  // §16.13: which clocks ticked at this time step; a second wake at one
  // time step, by another of the clocks, advances nothing again.
  SimTime now = ctx.CurrentTime();
  if (state.clocks.multiclock && state.advanced_at == now) return tick;
  // §16.14.6.3: a second pass of the Active region in one time step, after
  // the Reactive region wrote what a procedure reads, may queue instances
  // of a procedural assertion whose clock ticked earlier in the step; they
  // begin at this tick, and the attempts already advanced at it advance no
  // more.
  bool again = state.advanced_at == now;
  state.advanced_at = now;
  uint32_t ticked = ClocksTicked(state.clocks, now);
  if (ticked == 0) return tick;
  size_t beginning = (ticked & 1u) != 0 ? instances.size() : 0;
  tick.attempted = static_cast<uint32_t>(beginning);
  auto& samples = ctx.AssertionSamples();
  samples.SetClockTicks(ticked);
  for (const Expr* site : state.past_sites) EvalExpr(site, ctx, arena);
  if (disabled) {
    state.attempts.clear();
    samples.SetClockTicks(~0u);
    return tick;
  }
  size_t advanced = again ? state.attempts.size() : 0;
  for (size_t i = 0; i < beginning; ++i) {
    NodeState* attempt = NewNodeState(state.root, state, 0, arena);
    attempt->bindings = instances[i];
    state.attempts.push_back(attempt);
  }
  StepContext sc{state, ctx, arena, ticked};
  StepAttempts(sc, beginning, advanced, tick);
  samples.SetClockTicks(~0u);
  return tick;
}

std::vector<PropertyVerdict> FinishPropertyTree(PropertyTreeState& state) {
  std::vector<PropertyVerdict> verdicts;
  verdicts.reserve(state.attempts.size());
  for (NodeState* attempt : state.attempts) {
    Finish(state.root, *attempt);
    verdicts.push_back(VerdictOf(state.root, *attempt));
  }
  state.attempts.clear();
  return verdicts;
}

}  // namespace delta
