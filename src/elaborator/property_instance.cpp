#include "elaborator/property_instance.h"

#include <cstddef>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/expr_substitute.h"

namespace delta {

// §16.12.18: whether an actual argument of `instance` is a sequence_expr or
// a property_expr, which the boolean substitution does not read, so the
// instance is evaluated as the body's tree.
bool InstanceHasTreeActual(const Expr* instance) {
  if (instance == nullptr || instance->kind != ExprKind::kCall) return false;
  for (const Expr* arg : instance->args) {
    if (arg != nullptr && arg->property_actual != nullptr) return true;
  }
  return false;
}

// §16.12.18 by way of §16.8.1: one event of the instantiated property's
// clock with the actuals in the formals' places: the actual of a formal of
// type event, an edge keyword over a signal, supplies the edge and the
// signal, and any other actual the signal under the edge the clock wrote.
EventExpr SubstituteClockEvent(EventExpr ev, const ActualsByFormal& actuals,
                               Arena& arena) {
  ev.iff_condition = SubstituteFormals(ev.iff_condition, actuals, arena);
  if (ev.signal != nullptr && ev.signal->kind == ExprKind::kIdentifier) {
    auto it = actuals.find(ev.signal->text);
    const Expr* actual = it == actuals.end() ? nullptr : it->second;
    if (actual != nullptr && actual->kind == ExprKind::kUnary &&
        (actual->op == TokenKind::kKwPosedge ||
         actual->op == TokenKind::kKwNegedge ||
         actual->op == TokenKind::kKwEdge)) {
      ev.edge = actual->op == TokenKind::kKwPosedge   ? Edge::kPosedge
                : actual->op == TokenKind::kKwNegedge ? Edge::kNegedge
                                                      : Edge::kEdge;
      ev.signal = actual->lhs;
      return ev;
    }
  }
  ev.signal = SubstituteFormals(ev.signal, actuals, arena);
  return ev;
}

// The declaration `operand` instantiates where it names one of `kind`, an
// identifier or a call naming a sequence or a property.
const ModuleItem* InstantiatedDecl(const Expr* operand, ModuleItemKind kind,
                                   const PropertyRegistry& registry) {
  if (operand == nullptr) return nullptr;
  if (operand->kind != ExprKind::kIdentifier &&
      operand->kind != ExprKind::kCall) {
    return nullptr;
  }
  const ModuleItem* decl = registry.Find(
      operand->kind == ExprKind::kCall ? operand->callee : operand->text);
  return decl != nullptr && decl->kind == kind ? decl : nullptr;
}

// §16.12.2 and §16.13.4: a sequence declaration of one operand, an instance
// of the named sequence `instance` names, for the flattening to expand: a
// bare name in a property is a sequence where the name is a sequence's.
ModuleItem* SequenceInstanceBody(Expr* instance, Arena& arena) {
  auto* seq = arena.Create<ModuleItem>();
  seq->kind = ModuleItemKind::kSequenceDecl;
  seq->loc = instance->range.start;
  seq->seq_linear.operands.push_back(instance);
  SeqCycleDelay none;
  none.min = 0;
  none.max = 0;
  seq->seq_linear.delays.push_back(none);
  seq->seq_linear.match_items.emplace_back();
  seq->seq_linear.repetitions.emplace_back();
  return seq;
}

// §16.13.3 and §16.13.4: the clock flowing into a property declared with
// none: the clocking event its body's property_expr opens with, after the
// disable condition where §16.14.1's `abc` writes one, on the root where
// the body is a `not` and on the first operand of the sequence the body
// opens with where the body is a sequence or an implication, §16.14.2's
// `abc` writing its clock before the antecedent, from which it flows to the
// consequent; or else the clock of the sequence its body opens with, where
// that sequence, the body itself or the antecedent of the implication it
// is, is one instance of a sequence declared with a clock, `mult_s |=>
// mult_s` being on mult_s's; empty otherwise.
const std::vector<EventExpr>& FlowedBodyClock(
    const ModuleItem* decl, const PropertyRegistry& registry) {
  static const std::vector<EventExpr> kNone;
  const PropertyExprNode* root = decl->prop_body_tree;
  if (root == nullptr) return kNone;
  if (!root->clock.empty()) return root->clock;
  if (root->sequence == nullptr) return kNone;
  bool opens = root->kind == PropertyExprNode::Kind::kSequence ||
               root->kind == PropertyExprNode::Kind::kImplication;
  const SeqLinearBody& body = root->sequence->seq_linear;
  if (opens && !body.clocks.empty() && !body.clocks[0].empty()) {
    return body.clocks[0];
  }
  if (!opens || body.operands.size() != 1) return kNone;
  const ModuleItem* seq = InstantiatedDecl(
      body.operands[0], ModuleItemKind::kSequenceDecl, registry);
  return seq == nullptr ? kNone : seq->seq_clock;
}

// §16.13.4: a boolean operand of the tree that is the bare name of a named
// sequence, or a call of one, which the parser read as a boolean since a
// variable's name reads the same, is the sequence, a node the flattening
// expands; the walk reaches the trees an instance's actuals carry too.
void PromoteSequenceInstances(PropertyExprNode* node,
                              const PropertyRegistry& registry, Arena& arena) {
  if (node == nullptr) return;
  if (node->kind == PropertyExprNode::Kind::kBoolean &&
      node->boolean != nullptr &&
      InstantiatedDecl(node->boolean, ModuleItemKind::kSequenceDecl,
                       registry) != nullptr) {
    node->kind = PropertyExprNode::Kind::kSequence;
    node->sequence = SequenceInstanceBody(node->boolean, arena);
    node->boolean = nullptr;
  }
  if (node->boolean != nullptr && node->boolean->kind == ExprKind::kCall) {
    for (Expr* arg : node->boolean->args) {
      if (arg != nullptr) {
        PromoteSequenceInstances(arg->property_actual, registry, arena);
      }
    }
  }
  for (PropertyExprNode* operand : node->operands) {
    PromoteSequenceInstances(operand, registry, arena);
  }
}

// §16.14.7: the event expression of the inferred clock as an actual argument
// of an event formal writes it, an edge keyword over the signal, or the
// signal alone where the event names no edge; an iff, which no actual can
// carry, is left behind.
static Expr* ClockActual(const EventExpr& ev, Arena& arena) {
  if (ev.edge == Edge::kNone) return ev.signal;
  auto* actual = arena.Create<Expr>();
  actual->kind = ExprKind::kUnary;
  actual->op = ev.edge == Edge::kPosedge   ? TokenKind::kKwPosedge
               : ev.edge == Edge::kNegedge ? TokenKind::kKwNegedge
                                           : TokenKind::kKwEdge;
  actual->lhs = ev.signal;
  actual->range = ev.signal != nullptr ? ev.signal->range : SourceRange{};
  return actual;
}

// §16.14.7: the disable condition $inferred_disable returns outside the
// scope of any default disable iff declaration.
static Expr* FalseLiteral(Arena& arena) {
  static constexpr std::string_view kZero = "1'b0";
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->text = kZero;
  literal->int_val = 0;
  return literal;
}

// Whether any formal of `decl` is defaulted to an inferred function.
static bool HasInferredDefault(const ModuleItem* decl) {
  for (InferredDefault kind : decl->prop_formal_inferred) {
    if (kind != InferredDefault::kNone) return true;
  }
  return false;
}

// The actual the inferred function `kind` is replaced by at an instance, or
// nullptr where it is neither function or no clock is inferred there.
static Expr* InferredActual(InferredDefault kind,
                            const InferredAtInstance& inferred, Arena& arena) {
  if (kind == InferredDefault::kClock && !inferred.clock.empty()) {
    return ClockActual(inferred.clock[0], arena);
  }
  if (kind == InferredDefault::kDisable) {
    return inferred.disable != nullptr ? inferred.disable : FalseLiteral(arena);
  }
  return nullptr;
}

void FillInferredDefaults(Expr* instance, const ModuleItem* decl,
                          const InferredAtInstance& inferred, Arena& arena) {
  if (instance == nullptr || decl == nullptr || !HasInferredDefault(decl)) {
    return;
  }
  if (instance->kind == ExprKind::kIdentifier) {
    instance->kind = ExprKind::kCall;
    instance->callee = instance->text;
  }
  if (instance->kind != ExprKind::kCall) return;
  for (size_t i = 0; i < decl->prop_formal_inferred.size(); ++i) {
    if (instance->args.size() <= i) instance->args.push_back(nullptr);
    if (instance->args[i] != nullptr) continue;
    instance->args[i] =
        InferredActual(decl->prop_formal_inferred[i], inferred, arena);
  }
}

std::vector<EventExpr> DefaultClockingEvent(const RtlirModule* mod) {
  std::string_view named;
  if (mod == nullptr) return {};
  for (const ModuleItem* item : mod->clocking_blocks) {
    if (!item->is_default_clocking) continue;
    if (!item->clocking_event.empty()) return item->clocking_event;
    named = item->name;
  }
  for (const ModuleItem* item : mod->clocking_blocks) {
    if (!named.empty() && item->name == named &&
        !item->clocking_event.empty()) {
      return item->clocking_event;
    }
  }
  return {};
}

}  // namespace delta
