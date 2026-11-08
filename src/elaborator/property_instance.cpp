#include "elaborator/property_instance.h"

#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/semantic_leading_clocks.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

std::vector<EventExpr> BareFormalActualClock(const Expr* operand,
                                             const ActualsByFormal& actuals,
                                             const PropertyRegistry& registry,
                                             Arena& arena) {
  if (operand == nullptr || operand->kind != ExprKind::kIdentifier) return {};
  auto found = actuals.find(operand->text);
  if (found == actuals.end()) return {};
  return ActualLeadingClock(found->second, registry, arena);
}

std::vector<EventExpr> OpeningFormalActualClock(
    const SeqLinearBody& body, const ActualsByFormal& actuals,
    const PropertyRegistry& registry, Arena& arena) {
  if (body.operands.empty() ||
      (!body.clocks.empty() && !body.clocks[0].empty())) {
    return {};
  }
  return BareFormalActualClock(body.operands[0], actuals, registry, arena);
}

}  // namespace

namespace {

bool InstanceHasTreeActual(const Expr* instance) {
  if (instance == nullptr || instance->kind != ExprKind::kCall) return false;
  for (const Expr* arg : instance->args) {
    if (arg != nullptr && arg->property_actual != nullptr) return true;
  }
  return false;
}

bool BindsListToBoolean(const Expr* instance, const ModuleItem* decl) {
  const Expr* boolean = decl->prop_body_expr;
  if (boolean->kind != ExprKind::kIdentifier) return false;
  const ActualsByFormal kActuals = BindActuals(decl->prop_formals, instance);
  const auto kBound = kActuals.find(boolean->text);
  return kBound != kActuals.end() && kBound->second != nullptr &&
         kBound->second->sequence_reading != nullptr;
}

}  // namespace

bool TakesBooleanSubstitution(const Expr* instance, const ModuleItem* decl) {
  return decl->prop_body_expr != nullptr && !InstanceHasTreeActual(instance) &&
         !BindsListToBoolean(instance, decl);
}

std::vector<EventExpr> SubstituteClockEvents(
    const std::vector<EventExpr>& clock, const ActualsByFormal& actuals,
    Arena& arena) {
  std::vector<EventExpr> out;
  for (EventExpr ev : clock) {
    ev.iff_condition = SubstituteFormals(ev.iff_condition, actuals, arena);
    Expr* actual = nullptr;
    if (ev.signal != nullptr && ev.signal->kind == ExprKind::kIdentifier) {
      auto it = actuals.find(ev.signal->text);
      if (it != actuals.end()) actual = it->second;
    }
    if (IsEventActual(actual)) {
      AppendActualEvents(ev, actual, arena, out);
      continue;
    }
    ev.signal = SubstituteFormals(ev.signal, actuals, arena);
    out.push_back(ev);
  }
  return out;
}

std::vector<EventExpr> SequenceInstanceClock(const ModuleItem* seq,
                                             const Expr* instance,
                                             const PropertyRegistry& registry,
                                             Arena& arena) {
  ActualsByFormal actuals = BindActualsWithDefaults(
      seq->prop_formals, seq->prop_formal_defaults, instance);
  if (seq->seq_clock.empty()) {
    std::vector<EventExpr> clock =
        OpeningFormalActualClock(seq->seq_linear, actuals, registry, arena);
    if (!clock.empty()) return clock;
    return SubstituteClockEvents(DeterminedSequenceClock(seq, registry),
                                 actuals, arena);
  }
  return SubstituteClockEvents(seq->seq_clock, actuals, arena);
}

static std::vector<EventExpr> InstanceActualClock(
    const Expr* actual, const PropertyRegistry& registry, Arena& arena) {
  const ModuleItem* decl = registry.FindInstance(actual);
  if (decl == nullptr) return {};
  if (decl->kind == ModuleItemKind::kSequenceDecl) {
    return SequenceInstanceClock(decl, actual, registry, arena);
  }
  if (decl->kind != ModuleItemKind::kPropertyDecl) return {};
  ActualsByFormal actuals = BindActualsWithDefaults(
      decl->prop_formals, decl->prop_formal_defaults, actual);
  return PropertyInstanceClock(decl, actuals, registry, arena);
}

std::vector<EventExpr> PropertyInstanceClock(const ModuleItem* decl,
                                             const ActualsByFormal& actuals,
                                             const PropertyRegistry& registry,
                                             Arena& arena) {
  const std::vector<EventExpr>& clock = decl->prop_clock.empty()
                                            ? FlowedBodyClock(decl, registry)
                                            : decl->prop_clock;
  if (!clock.empty()) return SubstituteClockEvents(clock, actuals, arena);
  std::vector<EventExpr> from_actual =
      FormalOpeningClock(decl->prop_body_tree, actuals, registry, arena);
  if (!from_actual.empty()) return from_actual;
  return SubstituteClockEvents(
      DeterminedLeadingClock(decl->prop_body_tree, registry), actuals, arena);
}

std::vector<EventExpr> ActualLeadingClock(const Expr* actual,
                                          const PropertyRegistry& registry,
                                          Arena& arena) {
  if (actual == nullptr) return {};
  if (actual->property_actual == nullptr) {
    return InstanceActualClock(actual, registry, arena);
  }
  const PropertyExprNode* tree = actual->property_actual;
  if (!tree->clock.empty()) return tree->clock;
  std::vector<EventExpr> clocks = SemanticLeadingClocks(tree, {}, registry);
  if (clocks.size() != 1) return {};
  return clocks;
}

std::vector<EventExpr> FormalOpeningClock(const PropertyExprNode* body,
                                          const ActualsByFormal& actuals,
                                          const PropertyRegistry& registry,
                                          Arena& arena) {
  if (body == nullptr || !body->clock.empty()) return {};
  if (body->kind == PropertyExprNode::Kind::kBoolean) {
    return BareFormalActualClock(body->boolean, actuals, registry, arena);
  }
  bool opens = body->kind == PropertyExprNode::Kind::kSequence ||
               body->kind == PropertyExprNode::Kind::kImplication;
  if (!opens || body->sequence == nullptr) return {};
  return OpeningFormalActualClock(body->sequence->seq_linear, actuals, registry,
                                  arena);
}

const ModuleItem* InstantiatedDecl(const Expr* operand, ModuleItemKind kind,
                                   const PropertyRegistry& registry) {
  const ModuleItem* decl = registry.FindInstance(operand);
  return decl != nullptr && decl->kind == kind ? decl : nullptr;
}

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

static Expr* ClockActual(const std::vector<EventExpr>& clock, Arena& arena) {
  Expr* actual = nullptr;
  for (const EventExpr& ev : clock) {
    Expr* event = EventAsActual(ev, ev.signal->range.start, arena);
    actual =
        actual == nullptr ? event : EitherEventActual(actual, event, arena);
  }
  return actual;
}

static Expr* FalseLiteral(Arena& arena) {
  static constexpr std::string_view kZero = "1'b0";
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->text = kZero;
  literal->int_val = 0;
  return literal;
}

static bool HasInferredDefault(const ModuleItem* decl) {
  for (InferredDefault kind : decl->prop_formal_inferred) {
    if (kind != InferredDefault::kNone) return true;
  }
  return false;
}

static Expr* InferredActual(InferredDefault kind,
                            const InferredAtInstance& inferred, Arena& arena) {
  if (kind == InferredDefault::kClock && !inferred.clock.empty()) {
    return ClockActual(inferred.clock, arena);
  }
  if (kind == InferredDefault::kDisable) {
    return inferred.disable != nullptr ? inferred.disable : FalseLiteral(arena);
  }
  return nullptr;
}

static InferredDefault InferredDefaultCalled(const Expr* e) {
  if (e == nullptr || e->kind != ExprKind::kSystemCall) {
    return InferredDefault::kNone;
  }
  if (e->callee == "$inferred_clock") return InferredDefault::kClock;
  if (e->callee == "$inferred_disable") return InferredDefault::kDisable;
  return InferredDefault::kNone;
}

void FillInferredCheckerDefaults(RtlirModuleInst& inst,
                                 const InferredAtInstance& inferred,
                                 Arena& arena) {
  for (RtlirPortBinding& binding : inst.port_bindings) {
    Expr* actual = InferredActual(InferredDefaultCalled(binding.connection),
                                  inferred, arena);
    if (actual != nullptr) binding.connection = actual;
  }
}

void FillInferredDefaults(Expr* instance, const ModuleItem* decl,
                          const InferredAtInstance& inferred, Arena& arena,
                          DiagEngine* diag) {
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
    if (instance->args[i] == nullptr && diag != nullptr &&
        decl->prop_formal_inferred[i] == InferredDefault::kClock) {
      diag->Error(instance->range.start,
                  std::format("$inferred_clock, the default of the formal '{}' "
                              "of '{}', has no resolved clocking event at "
                              "this instance",
                              decl->prop_formals[i], decl->name),
                  Subclause("16.14.7"));
    }
  }
}

Expr* QualifiedInstance(Expr* instance, const PropertyRegistry& registry,
                        Arena& arena) {
  if (instance == nullptr || instance->kind != ExprKind::kMemberAccess ||
      instance->is_scope_resolution || instance->lhs == nullptr ||
      instance->rhs == nullptr ||
      instance->lhs->kind != ExprKind::kIdentifier ||
      instance->rhs->kind != ExprKind::kIdentifier) {
    return instance;
  }
  auto* qualified =
      arena.Create<std::string>(std::string(instance->lhs->text) + "." +
                                std::string(instance->rhs->text));
  if (registry.Find(*qualified) == nullptr) return instance;
  instance->kind = ExprKind::kIdentifier;
  instance->text = *qualified;
  instance->lhs = nullptr;
  instance->rhs = nullptr;
  return instance;
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
  return mod->inherited_default_clock;
}

void NameInstanceByKey(ModuleItem* item, Arena& arena) {
  Expr* instance = item->assert_expr;
  if (instance == nullptr) return;
  if (instance->kind == ExprKind::kCall && instance->callee.empty()) {
    instance->callee = item->prop_instance_name;
    return;
  }
  if (instance->kind != ExprKind::kMemberAccess) return;
  auto* name = arena.Create<Expr>();
  name->kind = ExprKind::kIdentifier;
  name->text = item->prop_instance_name;
  name->range = instance->range;
  item->assert_expr = name;
}

}  // namespace delta
